// Fast drop-in for make.fun's csv-reader 1.0.0, v3: escaped-byte transducer.
// JSON unescaping + CSV parsing + JSON serialization are fused into ONE pass over the raw
// cases.json bytes. The CSV text sits in the file as a JSON-escaped string, and the answer is
// JSON too, so almost every byte is copied verbatim from the input buffer to the output buffer:
//   \"  = a CSV quote (stays \" in the output)      \n = LF        \r\n = CRLF (one line)
//   \r alone outside quotes = stray_cr (dropped)    \r/\n inside quotes = \n in the output
//   \/ \\ \t \b \f and raw UTF-8 copy straight through (valid JSON escapes round-trip)
//   \uXXXX cannot be represented without decoding -> per-case bail to the string parser below.
// Field contents are byte spans, never JS strings; errors are parallel numeric arrays; rows are
// staged in a side buffer and assembled once per case (columns, rows, errors key order). The
// envelope is scanned by exact byte-matching of "input"/"text"/"header"; any structural surprise
// falls back to a whole-file JSON.parse + string run(). A malformed envelope or a raw control
// byte (impossible in valid JSON) takes the same whole-file bail.
//
// The string run(input) at the bottom is the v1 parser, verified exact against the reference
// reader (63/63); it serves the \u fallback and keeps the drop-in contract. Pure: no clock, no
// randomness, nothing kept between calls except reusable scratch buffers.

// --- byte constants ---------------------------------------------------------------
const BS = 92;   // backslash
const QT = 34;   // double quote
const CM = 44;   // comma
const OB = 91;   // [
const CB = 93;   // ]
const OC = 123;  // {
const CC = 125;  // }
const CO = 58;   // :
const NL = 110;  // 'n'
const CR = 114;  // 'r'
const UE = 117;  // 'u'

// --- scratch state (module-level, reused across cases; no per-case allocation) ----
let IN = null;          // raw cases.json bytes
let n = 0;              // IN length (envelope scan)
let ep = 0;             // envelope scan cursor

let OUT = Buffer.allocUnsafe(1 << 20);   // final answers bytes
let outU8 = OUT;
let outCap = OUT.length;
let op = 0;

let ST = Buffer.allocUnsafe(1 << 20);    // row staging (one case at a time)
let stU8 = ST;
let stCap = ST.length;
let sp = 0;

let EX = Buffer.allocUnsafe(1 << 16);    // long_row extra arrays, pre-serialized
let exU8 = EX;
let exCap = EX.length;
let extraOp = 0;

// Per-case parse state.
let p = 0;              // input cursor inside the text token
let tEnd = 0;           // text token content end (exclusive, before the closing quote)
let line = 1;           // current 1-based line
let recLine = 1;        // line the current record starts on
let recRow = -1;        // rows index of the current record (-1 = null, the header)
let width = -1;         // first record's field count
let headerFlag = false;
let haveColumns = false;
let rowCount = 0;       // staged rows (includes the header row when taken)
let errCount = 0;
let fc = 0;             // fields in the current row
let curRowStart = 0;    // ST offset of the current row's '['
let lastQuoted = false; // was the last field a quoted one
let lastAdded = 0;      // content bytes kept by the last unquoted read (quote_junk test)

// Row/field spans are absolute ST offsets; buffer growth preserves offsets (content is copied
// to the same positions in a larger buffer), so spans never need fixing up.
let rowStarts = new Int32Array(8192);
let fStarts = new Int32Array(512);
let fEnds = new Int32Array(512);

// Errors: 0=stray_cr 1=unterminated_quote 2=quote_junk 3=short_row 4=long_row.
// eA: short_row field count / long_row extra span start; eB: long_row extra span end.
let eCode = new Int32Array(4096);
let eLine = new Int32Array(4096);
let eRow = new Int32Array(4096);
let eA = new Int32Array(4096);
let eB = new Int32Array(4096);

// --- growth -----------------------------------------------------------------------
function needOut(k) {
  if (op + k > outCap) {
    let c = outCap;
    while (c < op + k) c *= 2;
    const nb = Buffer.allocUnsafe(c);
    nb.set(outU8.subarray(0, op));
    OUT = nb; outU8 = nb; outCap = c;
  }
}
function needSt(k) {
  if (sp + k > stCap) {
    let c = stCap;
    while (c < sp + k) c *= 2;
    const nb = Buffer.allocUnsafe(c);
    nb.set(stU8.subarray(0, sp));
    ST = nb; stU8 = nb; stCap = c;
  }
}
function needEx(k) {
  if (extraOp + k > exCap) {
    let c = exCap;
    while (c < extraOp + k) c *= 2;
    const nb = Buffer.allocUnsafe(c);
    nb.set(exU8.subarray(0, extraOp));
    EX = nb; exU8 = nb; exCap = c;
  }
}
function growRows() {
  const na = new Int32Array(rowStarts.length * 2);
  na.set(rowStarts);
  rowStarts = na;
}
function growFields() {
  const a = new Int32Array(fStarts.length * 2);
  a.set(fStarts);
  fStarts = a;
  const b = new Int32Array(fEnds.length * 2);
  b.set(fEnds);
  fEnds = b;
}
function growErrs() {
  const k = eCode.length * 2;
  let a = new Int32Array(k); a.set(eCode); eCode = a;
  a = new Int32Array(k); a.set(eLine); eLine = a;
  a = new Int32Array(k); a.set(eRow); eRow = a;
  a = new Int32Array(k); a.set(eA); eA = a;
  a = new Int32Array(k); a.set(eB); eB = a;
}
function pushErr(code, a, b) {
  if (errCount === eCode.length) growErrs();
  eCode[errCount] = code;
  eLine[errCount] = recLine;
  eRow[errCount] = recRow;
  eA[errCount] = a;
  eB[errCount] = b;
  errCount += 1;
}

// --- output primitives ------------------------------------------------------------
function putByte(c) { needOut(1); outU8[op++] = c; }
function putBuf(b) { needOut(b.length); outU8.set(b, op); op += b.length; }
function putInt(v) {
  needOut(12);
  if (v === 0) { outU8[op++] = 48; return; }
  const start = op;
  while (v > 0) { outU8[op++] = 48 + (v % 10); v = (v / 10) | 0; }
  let a = start;
  let b = op - 1;
  while (a < b) { const t = outU8[a]; outU8[a] = outU8[b]; outU8[b] = t; a += 1; b -= 1; }
}

const COLS_KEY = Buffer.from('{"columns":');
const ROWS_KEY = Buffer.from(',"rows":[');
const ERRS_KEY = Buffer.from('],"errors":[');
const ROW_KEY = Buffer.from(',"row":');
const FIELDS_KEY = Buffer.from(',"fields":');
const EXTRA_KEY = Buffer.from(',"extra":');
const NULL_BUF = Buffer.from('null');
const EMPTY_ARR = Buffer.from('[]');
const CLOSE_BUF = Buffer.from(']}');
const ERR_PREFIX = [
  Buffer.from('{"code":"stray_cr","line":'),
  Buffer.from('{"code":"unterminated_quote","line":'),
  Buffer.from('{"code":"quote_junk","line":'),
  Buffer.from('{"code":"short_row","line":'),
  Buffer.from('{"code":"long_row","line":'),
];
const CODE_IDX = { stray_cr: 0, unterminated_quote: 1, quote_junk: 2, short_row: 3, long_row: 4 };

// --- CSV parse on the JSON-escaped bytes ------------------------------------------
// Field endings: 0 = comma, 1 = line break, 2 = end of text; negative = bail out.

// Unquoted read from p: copies bytes to ST until comma / LF / CRLF / end. A lone \r is dropped
// (stray_cr). \u bails per case; a raw control byte (invalid JSON) bails whole-file. lastAdded
// counts kept content bytes (the quote_junk test only needs > 0).
function parseUnquoted() {
  lastAdded = 0;
  for (;;) {
    while (p + 4 <= tEnd) {
      const b0 = IN[p];
      const b1 = IN[p + 1];
      const b2 = IN[p + 2];
      const b3 = IN[p + 3];
      if (b0 !== BS && b1 !== BS && b2 !== BS && b3 !== BS &&
          b0 !== CM && b1 !== CM && b2 !== CM && b3 !== CM) {
        if (sp + 4 > stCap) needSt(4);
        stU8[sp] = b0; stU8[sp + 1] = b1; stU8[sp + 2] = b2; stU8[sp + 3] = b3;
        sp += 4; p += 4; lastAdded += 4;
        continue;
      }
      break;
    }
    if (p >= tEnd) return 2;
    const c = IN[p];
    if (c === CM) { p += 1; return 0; }
    if (c !== BS) {
      if (c < 32) return -2;
      if (sp + 1 > stCap) needSt(1);
      stU8[sp++] = c; p += 1; lastAdded += 1;
      continue;
    }
    if (p + 1 >= tEnd) return -2;
    const d = IN[p + 1];
    if (d === NL) { p += 2; line += 1; return 1; }
    if (d === CR) {
      if (p + 3 < tEnd && IN[p + 2] === BS && IN[p + 3] === NL) { p += 4; line += 1; return 1; }
      pushErr(0, 0, 0);
      p += 2;
      continue;
    }
    if (d === UE) return -1;
    // \/ \\ \" \t \b \f ...: a valid JSON escape round-trips verbatim.
    if (sp + 2 > stCap) needSt(2);
    stU8[sp++] = BS; stU8[sp++] = d; p += 2; lastAdded += 2;
  }
}

// Quoted field whose opening \" is at p. Single pass: content is emitted with doubled quotes
// collapsed and CR/LF normalized while watching for the closing (non-doubled) quote. If the
// quote never closes, the emitted content is rewound, unterminated_quote is recorded, a literal
// quote is emitted and the rest is re-read as unquoted — exactly the reference policy.
function parseQuoted() {
  const contentP = p + 2;
  const contentStart = sp;
  let lines = 0;
  let r = contentP;
  for (;;) {
    while (r + 4 <= tEnd) {
      const b0 = IN[r];
      const b1 = IN[r + 1];
      const b2 = IN[r + 2];
      const b3 = IN[r + 3];
      if (b0 !== BS && b1 !== BS && b2 !== BS && b3 !== BS) {
        if (sp + 4 > stCap) needSt(4);
        stU8[sp] = b0; stU8[sp + 1] = b1; stU8[sp + 2] = b2; stU8[sp + 3] = b3;
        sp += 4; r += 4;
        continue;
      }
      break;
    }
    if (r >= tEnd) {
      // Never closed: rewind, literal quote, re-read as unquoted from just after the opening.
      pushErr(1, 0, 0);
      sp = contentStart;
      if (sp + 2 > stCap) needSt(2);
      stU8[sp++] = BS; stU8[sp++] = QT;
      p = contentP;
      return parseUnquoted();
    }
    const c = IN[r];
    if (c !== BS) {
      if (c < 32) return -2;
      if (sp + 1 > stCap) needSt(1);
      stU8[sp++] = c; r += 1;
      continue;
    }
    if (r + 1 >= tEnd) return -2;
    const d = IN[r + 1];
    if (d === QT) {
      if (r + 3 < tEnd && IN[r + 2] === BS && IN[r + 3] === QT) {
        // Doubled quote: one quote character, still \" in the output.
        if (sp + 2 > stCap) needSt(2);
        stU8[sp++] = BS; stU8[sp++] = QT;
        r += 4;
        continue;
      }
      // Closing quote.
      line += lines;
      p = r + 2;
      if (p >= tEnd) return 2;
      const e = IN[p];
      if (e === CM) { p += 1; return 0; }
      if (e === BS) {
        if (p + 1 >= tEnd) return -2;
        const f = IN[p + 1];
        if (f === NL) { p += 2; line += 1; return 1; }
        if (f === CR && p + 3 < tEnd && IN[p + 2] === BS && IN[p + 3] === NL) {
          p += 4; line += 1; return 1;
        }
      }
      // Trailing junk up to the next comma / line break is appended as it stands.
      const ended = parseUnquoted();
      if (ended < 0) return ended;
      if (lastAdded > 0) pushErr(2, 0, 0);
      return ended;
    }
    if (d === NL) {
      lines += 1;
      if (sp + 2 > stCap) needSt(2);
      stU8[sp++] = BS; stU8[sp++] = NL;
      r += 2;
      continue;
    }
    if (d === CR) {
      lines += 1;
      if (sp + 2 > stCap) needSt(2);
      stU8[sp++] = BS; stU8[sp++] = NL;
      r += (r + 3 < tEnd && IN[r + 2] === BS && IN[r + 3] === NL) ? 4 : 2;
      continue;
    }
    if (d === UE) return -1;
    if (sp + 2 > stCap) needSt(2);
    stU8[sp++] = BS; stU8[sp++] = d;
    r += 2;
  }
}

// One field: writes its JSON string token (quotes included) to ST, records the content span.
function parseField() {
  if (fc === fStarts.length) growFields();
  if (sp + 1 > stCap) needSt(1);
  stU8[sp++] = QT;
  const contentStart = sp;
  let ended;
  if (p + 1 < tEnd && IN[p] === BS && IN[p + 1] === QT) {
    lastQuoted = true;
    ended = parseQuoted();
  } else {
    lastQuoted = false;
    ended = parseUnquoted();
  }
  if (ended < 0) return ended;
  if (sp + 1 > stCap) needSt(1);
  stU8[sp++] = QT;
  fStarts[fc] = contentStart;
  fEnds[fc] = sp - 1;
  fc += 1;
  return ended;
}

// Record end: blank-record skip, width fix-up (short pad / long cut), stage the row.
function endRow() {
  // A line left with no characters is no record (its errors stay).
  if (fc === 1 && !lastQuoted && fEnds[0] === fStarts[0]) {
    sp = curRowStart;
    fc = 0;
    return;
  }
  if (width < 0) width = fc;
  if (headerFlag && !haveColumns) {
    haveColumns = true;
  } else if (fc < width) {
    pushErr(3, fc, 0);
    needSt(3 * (width - fc));
    while (fc < width) {
      stU8[sp++] = CM; stU8[sp++] = QT; stU8[sp++] = QT;
      fc += 1;
    }
  } else if (fc > width) {
    const exStart = extraOp;
    needEx(1);
    exU8[extraOp++] = OB;
    for (let i = width; i < fc; i += 1) {
      if (i > width) { needEx(1); exU8[extraOp++] = CM; }
      const s = fStarts[i] - 1;
      const e = fEnds[i] + 1;
      needEx(e - s);
      exU8.set(stU8.subarray(s, e), extraOp);
      extraOp += e - s;
    }
    needEx(1);
    exU8[extraOp++] = CB;
    pushErr(4, exStart, extraOp);
    sp = fEnds[width - 1] + 1;
    fc = width;
  }
  if (sp + 1 > stCap) needSt(1);
  stU8[sp++] = CB;
  if (rowCount === rowStarts.length) growRows();
  rowStarts[rowCount] = curRowStart;
  rowCount += 1;
  fc = 0;
}

// The record loop over one text token. Returns 0, or a negative bail code.
function parseTextCase() {
  // A U+FEFF at the very start, stored as raw UTF-8, is dropped. (\uFEFF bails per case.)
  if (p + 2 < tEnd && IN[p] === 0xef && IN[p + 1] === 0xbb && IN[p + 2] === 0xbf) p += 3;
  for (;;) {
    // Lines with no characters are no records.
    for (;;) {
      if (p >= tEnd) break;
      if (IN[p] !== BS) break;
      if (p + 1 >= tEnd) return -2;
      const d = IN[p + 1];
      if (d === NL) { p += 2; line += 1; continue; }
      if (d === CR && p + 3 < tEnd && IN[p + 2] === BS && IN[p + 3] === NL) {
        p += 4; line += 1; continue;
      }
      break;
    }
    if (p >= tEnd) break;

    recLine = line;
    recRow = (headerFlag && !haveColumns) ? -1 : rowCount - ((headerFlag && haveColumns) ? 1 : 0);
    curRowStart = sp;
    if (sp + 1 > stCap) needSt(1);
    stU8[sp++] = OB;
    fc = 0;
    let ended;
    do {
      ended = parseField();
      if (ended < 0) return ended;
      if (ended === 0) {
        if (sp + 1 > stCap) needSt(1);
        stU8[sp++] = CM;
      }
    } while (ended === 0);
    endRow();
    if (ended === 2) break;
  }
  return 0;
}

// --- case assembly ------------------------------------------------------------------
function copyRow(i) {
  const s = rowStarts[i];
  const e = (i + 1 < rowCount) ? rowStarts[i + 1] : sp;
  needOut(e - s);
  outU8.set(ST.subarray(s, e), op);
  op += e - s;
}

// Assemble {"columns":...,"rows":[...],"errors":[...]} at caseStart from the staged rows and
// the numeric error arrays. Staging lives in ST, so these copies never overlap their sources.
function finalizeCase(caseStart) {
  op = caseStart;
  putBuf(COLS_KEY);
  if (!headerFlag) putBuf(NULL_BUF);
  else if (haveColumns) copyRow(0);
  else putBuf(EMPTY_ARR);
  putBuf(ROWS_KEY);
  const first = (headerFlag && haveColumns) ? 1 : 0;
  for (let i = first; i < rowCount; i += 1) {
    if (i > first) putByte(CM);
    copyRow(i);
  }
  putBuf(ERRS_KEY);
  for (let i = 0; i < errCount; i += 1) {
    if (i > 0) putByte(CM);
    const code = eCode[i];
    putBuf(ERR_PREFIX[code]);
    putInt(eLine[i]);
    putBuf(ROW_KEY);
    if (eRow[i] < 0) putBuf(NULL_BUF);
    else putInt(eRow[i]);
    if (code === 3) { putBuf(FIELDS_KEY); putInt(eA[i]); }
    else if (code === 4) {
      putBuf(EXTRA_KEY);
      const s = eA[i];
      const e = eB[i];
      needOut(e - s);
      outU8.set(EX.subarray(s, e), op);
      op += e - s;
    }
    putByte(CC);
  }
  putBuf(CLOSE_BUF);
}

// --- envelope scan ------------------------------------------------------------------
const K_INPUT = [105, 110, 112, 117, 116];        // input
const K_TEXT = [116, 101, 120, 116];              // text
const K_HEADER = [104, 101, 97, 100, 101, 114];   // header

function keyIs(buf, at, word) {
  if (buf[at] !== QT) return false;
  for (let i = 0; i < word.length; i += 1) {
    if (buf[at + 1 + i] !== word[i]) return false;
  }
  return buf[at + 1 + word.length] === QT;
}

// End (exclusive, past the closing quote) of the JSON string token opening at from.
// Native indexOf jumps over clean runs; only backslash/quote positions are visited in JS.
function strEnd(buf, from) {
  let q = from + 1;
  for (;;) {
    const qt = buf.indexOf(QT, q);
    if (qt < 0) return -1;
    const bs = buf.indexOf(BS, q);
    if (bs < 0 || qt < bs) return qt + 1;
    q = bs + 2;
  }
}

// Locate every case's text token and header literal. Returns null on any structural surprise
// (the caller then falls back to a whole-file JSON.parse). Keys match by exact bytes; escaped
// or reordered keys, missing text, non-literal header all take the fallback, which reproduces
// JSON.parse semantics exactly.
function scanCases(buf) {
  n = buf.length;
  ep = 0;
  const starts = [];
  const ends = [];
  const headers = [];
  const ws = () => {
    while (ep < n) {
      const c = buf[ep];
      if (c === 32 || c === 9 || c === 10 || c === 13) ep += 1;
      else break;
    }
  };
  const skipValue = () => {
    ws();
    const c = buf[ep];
    if (c === QT) {
      const e = strEnd(buf, ep);
      if (e < 0) throw 0;
      ep = e;
      return;
    }
    if (c === OC || c === OB) {
      const close = c === OC ? CC : CB;
      let depth = 1;
      ep += 1;
      while (depth > 0) {
        if (ep >= n) throw 0;
        const ch = buf[ep];
        if (ch === QT) {
          const e = strEnd(buf, ep);
          if (e < 0) throw 0;
          ep = e;
          continue;
        }
        if (ch === c) depth += 1;
        else if (ch === close) depth -= 1;
        ep += 1;
      }
      return;
    }
    while (ep < n) {
      const ch = buf[ep];
      if (ch === CM || ch === CC || ch === CB || ch === 32 || ch === 9 || ch === 10 || ch === 13) return;
      ep += 1;
    }
  };
  try {
    ws();
    if (buf[ep] !== OB) return null;
    ep += 1;
    ws();
    if (buf[ep] === CB) { ep += 1; ws(); return ep === n ? { starts, ends, headers } : null; }
    for (;;) {
      if (buf[ep] !== OC) return null;
      ep += 1;
      ws();
      let ts = -1;
      let te = -1;
      let hd = false;
      if (buf[ep] !== CC) {
        for (;;) {
          if (buf[ep] !== QT) return null;
          const isInput = keyIs(buf, ep, K_INPUT);
          const ke = strEnd(buf, ep);
          if (ke < 0) return null;
          ep = ke;
          ws();
          if (buf[ep] !== CO) return null;
          ep += 1;
          ws();
          if (isInput) {
            if (buf[ep] !== OC) return null;
            ep += 1;
            ws();
            if (buf[ep] !== CC) {
              for (;;) {
                if (buf[ep] !== QT) return null;
                const isText = keyIs(buf, ep, K_TEXT);
                const isHeader = !isText && keyIs(buf, ep, K_HEADER);
                const ike = strEnd(buf, ep);
                if (ike < 0) return null;
                ep = ike;
                ws();
                if (buf[ep] !== CO) return null;
                ep += 1;
                ws();
                if (isText) {
                  if (buf[ep] !== QT) return null;
                  ts = ep + 1;
                  const e = strEnd(buf, ep);
                  if (e < 0) return null;
                  te = e - 1;
                  ep = e;
                } else if (isHeader) {
                  if (buf[ep] === 116) { // true
                    if (buf[ep + 1] !== 114 || buf[ep + 2] !== 117 || buf[ep + 3] !== 101) return null;
                    ep += 4;
                    hd = true;
                  } else if (buf[ep] === 102) { // false
                    if (buf[ep + 1] !== 97 || buf[ep + 2] !== 108 || buf[ep + 3] !== 115 || buf[ep + 4] !== 101) return null;
                    ep += 5;
                    hd = false;
                  } else return null;
                } else skipValue();
                ws();
                if (buf[ep] === CM) { ep += 1; ws(); continue; }
                if (buf[ep] === CC) break;
                return null;
              }
            }
            ep += 1; // '}' of input
            ws();
          } else skipValue();
          ws();
          if (buf[ep] === CM) { ep += 1; ws(); continue; }
          if (buf[ep] === CC) break;
          return null;
        }
      }
      ep += 1; // '}' of the case
      if (ts < 0) return null;
      starts.push(ts);
      ends.push(te);
      headers.push(hd);
      ws();
      if (buf[ep] === CM) { ep += 1; ws(); continue; }
      if (buf[ep] === CB) break;
      return null;
    }
    ep += 1; // past the closing ']' of the array
    ws();
    if (ep !== n) return null;
    return { starts, ends, headers };
  } catch (e) {
    return null;
  }
}

// --- whole pipeline -----------------------------------------------------------------
function parseCaseBytes(ts, te, hd) {
  p = ts;
  tEnd = te;
  line = 1;
  recLine = 1;
  recRow = -1;
  width = -1;
  headerFlag = hd;
  haveColumns = false;
  rowCount = 0;
  errCount = 0;
  extraOp = 0;
  sp = 0;
  fc = 0;
  return parseTextCase();
}

// String-answer serializer for the fallback paths (JSON.stringify-compatible bytes).
const escRe = /[\ud800-\udbff][\udc00-\udfff]|["\\\u0000-\u001f\ud800-\udfff]/g;
function escString(s) {
  return s.replace(escRe, (m) => {
    if (m.length === 2) return m;
    switch (m) {
      case '"': return '\\"';
      case '\\': return '\\\\';
      case '\b': return '\\b';
      case '\t': return '\\t';
      case '\n': return '\\n';
      case '\f': return '\\f';
      case '\r': return '\\r';
      default: return '\\u' + m.charCodeAt(0).toString(16).padStart(4, '0');
    }
  });
}
function putEscaped(s) {
  const b = Buffer.from(escString(s), 'utf8');
  needOut(b.length);
  outU8.set(b, op);
  op += b.length;
}
function putFieldList(fs) {
  putByte(OB);
  for (let i = 0; i < fs.length; i += 1) {
    if (i > 0) putByte(CM);
    putByte(QT);
    putEscaped(fs[i]);
    putByte(QT);
  }
  putByte(CB);
}
function serializeAnswerBytes(ans) {
  putBuf(COLS_KEY);
  if (ans.columns === null) putBuf(NULL_BUF);
  else putFieldList(ans.columns);
  putBuf(ROWS_KEY);
  for (let r = 0; r < ans.rows.length; r += 1) {
    if (r > 0) putByte(CM);
    putFieldList(ans.rows[r]);
  }
  putBuf(ERRS_KEY);
  for (let i = 0; i < ans.errors.length; i += 1) {
    if (i > 0) putByte(CM);
    const e = ans.errors[i];
    putBuf(ERR_PREFIX[CODE_IDX[e.code]]);
    putInt(e.line);
    putBuf(ROW_KEY);
    if (e.row === null) putBuf(NULL_BUF);
    else putInt(e.row);
    if (e.fields !== undefined) { putBuf(FIELDS_KEY); putInt(e.fields); }
    if (e.extra !== undefined) { putBuf(EXTRA_KEY); putFieldList(e.extra); }
    putByte(CC);
  }
  putBuf(CLOSE_BUF);
}

function wholeFileFallback(buf) {
  const cases = JSON.parse(buf.toString('utf8'));
  op = 0;
  putByte(OB);
  for (let i = 0; i < cases.length; i += 1) {
    if (i > 0) putByte(CM);
    serializeAnswerBytes(run(cases[i].input));
  }
  putByte(CB);
  return OUT.subarray(0, op);
}

/** The v3 pipeline: raw cases.json Buffer in, answers.json Buffer out. */
export function runCasesBuffer(buf) {
  IN = buf;
  const env = scanCases(buf);
  const want = buf.length + (buf.length >> 2) + 4096;
  if (outCap < want) {
    OUT = Buffer.allocUnsafe(want);
    outU8 = OUT;
    outCap = want;
  }
  op = 0;
  if (env === null) return wholeFileFallback(buf);
  putByte(OB);
  for (let i = 0; i < env.starts.length; i += 1) {
    if (i > 0) putByte(CM);
    const caseStart = op;
    const st = parseCaseBytes(env.starts[i], env.ends[i], env.headers[i]);
    if (st === 0) {
      finalizeCase(caseStart);
    } else if (st === -1) {
      // \uXXXX somewhere in this case: decode just this token and use the string parser.
      op = caseStart;
      const text = JSON.parse(buf.toString('utf8', env.starts[i] - 1, env.ends[i] + 1));
      serializeAnswerBytes(run({ text, header: env.headers[i] }));
    } else {
      return wholeFileFallback(buf);
    }
  }
  putByte(CB);
  return OUT.subarray(0, op);
}

// --- string fallback: the v1 parser (verified exact 63/63 vs the reference reader) -----------
const COMMA = 0;
const LINE_BREAK = 1;
const END = 2;

// A span is packed as start * MUL + end, exact in a double while start,end < 2^26 (MUL = 2^26,
// product < 2^52). Texts at or above the limit fall back to plain slices so packing stays lossless.
const MUL = 67108864;

export function run(input) {
  const text = String(input.text);
  const ans = parse(text, input.header === true);
  // Materialize every packed span back to a verbatim slice; strings pass through unchanged.
  const cols = ans.columns;
  if (cols !== null) for (let i = 0; i < cols.length; i += 1) {
    const f = cols[i];
    if (typeof f === 'number') { const s = (f / MUL) | 0; cols[i] = text.slice(s, f - s * MUL); }
  }
  const rows = ans.rows;
  for (let r = 0; r < rows.length; r += 1) {
    const row = rows[r];
    for (let i = 0; i < row.length; i += 1) {
      const f = row[i];
      if (typeof f === 'number') { const s = (f / MUL) | 0; row[i] = text.slice(s, f - s * MUL); }
    }
  }
  const errors = ans.errors;
  for (let e = 0; e < errors.length; e += 1) {
    const extra = errors[e].extra;
    if (extra !== undefined) for (let i = 0; i < extra.length; i += 1) {
      const f = extra[i];
      if (typeof f === 'number') { const s = (f / MUL) | 0; extra[i] = text.slice(s, f - s * MUL); }
    }
  }
  return ans;
}

function parse(text, header) {
  const len = text.length;
  const spanMode = len < MUL;
  const errors = [];
  const rows = [];
  let columns = null;
  let width = -1;
  let pos = text.charCodeAt(0) === 0xfeff ? 1 : 0;
  let line = 1;
  let recordLine = 1;
  let recordRow = null;
  let fValue = '';
  let fEnded = END;
  let fAdded = 0;

  // Cached first-delimiter indices at or after pos; -1 forces a recompute. Each recompute is a
  // native indexOf scanning forward only, so total scanning is amortized O(text) per delimiter.
  let nextComma = -1;
  let nextLF = -1;
  let nextCR = -1;

  // Assemble a field from a prefix, optional stray-CR-split parts, and the final [s,e) run.
  // Returns a packed span when the value is a verbatim run with no prefix; a string otherwise.
  function finish(prefix, parts, s, e) {
    if (parts === null) {
      if (s === e) return prefix;
      if (prefix === '') return spanMode ? s * MUL + e : text.slice(s, e);
      const head = typeof prefix === 'number'
        ? text.slice((prefix / MUL) | 0, prefix - ((prefix / MUL) | 0) * MUL)
        : prefix;
      return head + text.slice(s, e);
    }
    const tail = s < e ? text.slice(s, e) : '';
    if (tail !== '') parts.push(tail);
    const joined = parts.join('');
    if (prefix === '') return joined;
    const head = typeof prefix === 'number'
      ? text.slice((prefix / MUL) | 0, prefix - ((prefix / MUL) | 0) * MUL)
      : prefix;
    return head + joined;
  }

  // Unquoted read from pos: a CR not followed by LF is dropped (stray_cr). Sets fValue/fEnded/fAdded.
  function readUnquoted(prefix) {
    let s = pos;
    let added = 0;
    let parts = null;
    while (pos < len) {
      if (nextComma < pos) { nextComma = text.indexOf(',', pos); if (nextComma < 0) nextComma = len; }
      if (nextLF < pos) { nextLF = text.indexOf('\n', pos); if (nextLF < 0) nextLF = len; }
      if (nextCR < pos) { nextCR = text.indexOf('\r', pos); if (nextCR < 0) nextCR = len; }
      if (nextComma <= nextLF && nextComma <= nextCR) {
        if (nextComma === len) {
          added += len - pos;
          pos = len;
          fValue = finish(prefix, parts, s, len);
          fEnded = END;
          fAdded = added;
          return;
        }
        added += nextComma - pos;
        fValue = finish(prefix, parts, s, nextComma);
        pos = nextComma + 1;
        fEnded = COMMA;
        fAdded = added;
        return;
      }
      if (nextCR < nextLF) {
        if (text.charCodeAt(nextCR + 1) === 10) {
          added += nextCR - pos;
          fValue = finish(prefix, parts, s, nextCR);
          pos = nextCR + 2;
          line += 1;
          fEnded = LINE_BREAK;
          fAdded = added;
          return;
        }
        errors.push({ code: 'stray_cr', line: recordLine, row: recordRow });
        added += nextCR - pos;
        if (parts === null) parts = [];
        if (nextCR > s) parts.push(text.slice(s, nextCR));
        pos = nextCR + 1;
        s = pos;
        continue;
      }
      added += nextLF - pos;
      fValue = finish(prefix, parts, s, nextLF);
      pos = nextLF + 1;
      line += 1;
      fEnded = LINE_BREAK;
      fAdded = added;
      return;
    }
    fValue = finish(prefix, parts, s, pos);
    fEnded = END;
    fAdded = added;
  }

  // Value of the quoted segment [s,e): count its lines; a verbatim segment stays a span, a segment
  // holding CR is materialized with CRLF/lone CR normalized to LF.
  function segValue(s, e) {
    if (s >= e) return '';
    const cr = text.indexOf('\r', s);
    if (cr < 0 || cr >= e) {
      let nl = text.indexOf('\n', s);
      while (nl >= 0 && nl < e) {
        line += 1;
        nl = text.indexOf('\n', nl + 1);
      }
      return spanMode ? s * MUL + e : text.slice(s, e);
    }
    let out = '';
    let runStart = s;
    let i = s;
    while (i < e) {
      const c = text.charCodeAt(i);
      if (c === 13) {
        out += text.slice(runStart, i) + '\n';
        line += 1;
        i += text.charCodeAt(i + 1) === 10 ? 2 : 1;
        runStart = i;
      } else {
        if (c === 10) line += 1;
        i += 1;
      }
    }
    return out + text.slice(runStart, e);
  }

  // A span-or-string field value as a plain string (for the rare doubled-quote join path).
  function asStr(v) {
    if (typeof v !== 'number') return v;
    const s = (v / MUL) | 0;
    return text.slice(s, v - s * MUL);
  }

  // Quoted field whose opening quote is at pos. An unclosed quote is literal: re-read as unquoted.
  function readQuoted() {
    const open = pos;
    const openLine = line;
    let s = open + 1;
    let parts = null;
    let q = text.indexOf('"', s);
    while (q >= 0) {
      if (text.charCodeAt(q + 1) === 34) {
        const sv = segValue(s, q);
        if (parts === null) parts = [asStr(sv), '"'];
        else parts.push(asStr(sv), '"');
        s = q + 2;
        q = text.indexOf('"', s);
        continue;
      }
      const sv = segValue(s, q);
      if (parts === null) fValue = sv;
      else {
        parts.push(asStr(sv));
        fValue = parts.join('');
      }
      pos = q + 1;
      if (pos >= len) {
        fEnded = END;
        return;
      }
      const c = text.charCodeAt(pos);
      if (c === 44) {
        pos += 1;
        fEnded = COMMA;
        return;
      }
      if (c === 10) {
        pos += 1;
        line += 1;
        fEnded = LINE_BREAK;
        return;
      }
      if (c === 13 && text.charCodeAt(pos + 1) === 10) {
        pos += 2;
        line += 1;
        fEnded = LINE_BREAK;
        return;
      }
      readUnquoted(fValue);
      if (fAdded > 0) errors.push({ code: 'quote_junk', line: recordLine, row: recordRow });
      return;
    }
    pos = open + 1;
    line = openLine;
    errors.push({ code: 'unterminated_quote', line: recordLine, row: recordRow });
    readUnquoted('"');
  }

  while (true) {
    // Lines with no characters are no records (lone CR is not skipped here).
    while (pos < len) {
      const c = text.charCodeAt(pos);
      if (c === 10) {
        pos += 1;
        line += 1;
      } else if (c === 13 && text.charCodeAt(pos + 1) === 10) {
        pos += 2;
        line += 1;
      } else {
        break;
      }
    }
    if (pos >= len) break;

    recordLine = line;
    recordRow = header && columns === null ? null : rows.length;
    const fields = [];
    let quoted;
    do {
      quoted = text.charCodeAt(pos) === 34;
      if (quoted) readQuoted();
      else readUnquoted('');
      fields.push(fValue);
    } while (fEnded === COMMA);

    // A line that held only stray CRs is left with no characters: no record.
    if (fields.length === 1 && fields[0] === '' && !quoted) continue;

    if (width < 0) width = fields.length;
    if (header && columns === null) {
      columns = fields;
      continue;
    }
    if (fields.length < width) {
      errors.push({ code: 'short_row', line: recordLine, row: recordRow, fields: fields.length });
      while (fields.length < width) fields.push('');
    } else if (fields.length > width) {
      errors.push({ code: 'long_row', line: recordLine, row: recordRow, extra: fields.splice(width) });
    }
    rows.push(fields);
  }
  return { columns: header ? (columns ?? []) : null, rows, errors };
}

// --- pre-warm -----------------------------------------------------------------------
// Run the transducer a few times on tiny synthetic data covering every branch (header on/off,
// BOM, CRLF/LF, doubled quotes, CR inside quotes, stray CR, unterminated quote, quote junk,
// short/long rows with quoted extras, blank lines, reordered keys, \u bail, whole-file bail) so
// the real run executes already-compiled, type-specialized code. No case data is retained.
const warmCases =
  '{"id":"w0","input":{"text":"a,b,c\\n1,2,3\\n4,5,6\\n","header":true}},' +
  '{"input":{"header":false,"text":"\uFEFFh1,h2\\r\\nx,\\"q\\"\\"q\\r\\nz\\",y\\r\\nshort\\r\\n1,2,\\"3,3\\",4\\n\\n\\r\\n"}},' +
  '{"id":"w2","input":{"text":"a,\\"unclosed\\nb,c\\nd,\\"junk\\"zz,e\\nf\\rg,h\\nz,\\"tail","header":false}},' +
  '{"id":"w3","input":{"text":"a,\\"x\\"y,b\\n\\"\\",\\"\\"\\n,\\n\\u00e9,\\u0001\\n","header":true}}';
const WARM_BUF = Buffer.from('[' + new Array(16).fill(warmCases).join(',') + ']');
for (let i = 0; i < 3; i += 1) runCasesBuffer(WARM_BUF);
runCasesBuffer(Buffer.from('[{"input":{"header":true}}]'));
