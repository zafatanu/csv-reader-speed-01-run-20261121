// Fast drop-in for make.fun's csv-reader 1.0.0, v2: fused span transducer core.
// Same broken-row policy as v1 (proven exact), but the scanner hoists delimiter discovery into
// cached native indexOf() calls (amortized O(text) native scanning, no per-char JS loop) and a
// field is a packed [start,end) span over the decoded text until it is transformed (doubled
// quotes, CR normalization, junk concatenation, stray-CR splits) — only then is a string built.
// run() materializes the spans back to plain strings (the scorer/diff-test contract); spans()
// hands the raw span answer to main.ts's manual serializer. Pure: nothing kept between calls.

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

// Span answer over the decoded text: {columns, rows, errors} where a field is either a packed
// span (number) or an already-materialized string. main.ts serializes directly from this.
export function spans(text, header) {
  return parse(text, header);
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