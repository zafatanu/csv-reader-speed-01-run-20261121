// csv-reader 1.0.0 fast drop-in, v2 driver: envelope scan + manual span serializer.
// cases.json is read WITHOUT a full-document JSON.parse: an escape-aware scan (cached native
// indexOf for " and \) locates each case's text token, native JSON.parse decodes ONLY that token,
// and header is read as a literal. Answers are emitted straight from solve.js's spans() over the
// decoded text: a span holding no JSON-dirty character (", \, U+0000-U+001F, lone surrogate) is
// copied verbatim; dirty spans are escaped by a pair-first regex replace that matches
// JSON.stringify byte for byte (well-formed surrogate pairs stay verbatim, lone ones become
// \uXXXX, short escapes \b \t \n \f \r, other control chars \u00XX lowercase). No field strings,
// row arrays, or answers object are ever built. Output shape is unchanged: a JSON array of BARE
// run() values in case order. CSV_V2_BENCH=1 prints a stage split (ms) to stderr for the dev bench.

import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { setFlagsFromString } from 'node:v8';

// V8's incremental marking off, set before solve.js is imported so all of its work runs under it.
setFlagsFromString('--no-incremental-marking');

type Field = number | string;
interface Answer {
  columns: Field[] | null;
  rows: Field[][];
  errors: { code: string; line: number; row: number | null; fields?: number; extra?: Field[] }[];
}

/** solve.js's span path: fields are packed spans (start * MUL + end) or materialized strings. */
const { spans } = (await import(new URL('./solve.js', import.meta.url).href)) as {
  spans: (text: string, header: boolean) => Answer;
};

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Must match solve.js's span packing (start * 2^26 + end, exact while start,end < 2^26).
const MUL = 67108864;

const BENCH = process.env.CSV_V2_BENCH === '1';
let tEnv = 0;
let tTok = 0;
let tParse = 0;
let tSer = 0;

// --- manual serializer -------------------------------------------------------------

// Any surrogate is flagged here (pairs too); the escaper below emits well-formed pairs verbatim,
// so over-detection only costs speed on emoji-heavy spans, never correctness.
const dirtyRe = /["\\\u0000-\u001f\ud800-\udfff]/g;

// Pair-first: a well-formed surrogate pair is consumed whole and kept verbatim; every other
// match is a single character JSON.stringify escapes. Escapes only, no literal newline.
const escRe = /[\ud800-\udbff][\udc00-\udfff]|["\\\u0000-\u001f\ud800-\udfff]/g;

/** JSON.stringify's string escaping, byte for byte (lowercase \uXXXX, short escapes). */
export function esc(s: string): string {
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

/** End (exclusive, past the closing quote) of the JSON string token opening at start. */
function strEnd(s: string, start: number): number {
  let p = start + 1;
  for (;;) {
    const q = s.indexOf('"', p);
    // A quote is a boundary only when an even run of backslashes precedes it. Counting
    // backwards from each candidate quote visits every backslash at most once overall.
    let b = q - 1;
    let n = 0;
    while (b >= p && s.charCodeAt(b) === 92) { n += 1; b -= 1; }
    if ((n & 1) === 0) return q + 1;
    p = q + 1;
  }
}

// --- envelope scan -----------------------------------------------------------------

export interface Envelope {
  starts: number[];
  ends: number[];
  headers: boolean[];
}

/** Locate every case's text token and header literal in the raw cases.json, no full parse. */
export function scanEnvelope(raw: string): Envelope {
  const starts: number[] = [];
  const ends: number[] = [];
  const headers: boolean[] = [];
  let p = 0;
  const ws = () => {
    for (;;) {
      const c = raw.charCodeAt(p);
      if (c === 32 || c === 9 || c === 10 || c === 13) p += 1;
      else return;
    }
  };
  // Skip one JSON value of any shape (strings escape-aware, containers depth-counted).
  const skipValue = () => {
    ws();
    const c = raw.charCodeAt(p);
    if (c === 34) { p = strEnd(raw, p); return; }
    if (c === 123 || c === 91) {
      const close = c === 123 ? 125 : 93;
      let depth = 1;
      p += 1;
      while (depth > 0) {
        const ch = raw.charCodeAt(p);
        if (ch === 34) { p = strEnd(raw, p); continue; }
        if (ch === c) depth += 1;
        else if (ch === close) depth -= 1;
        p += 1;
      }
      return;
    }
    for (;;) {
      const ch = raw.charCodeAt(p);
      if (ch === 44 || ch === 125 || ch === 93 || ch === 32 || ch === 9 || ch === 10 || ch === 13 || Number.isNaN(ch)) return;
      p += 1;
    }
  };
  // Read one object member key, leaving p at the value (after ':' and whitespace).
  const key = () => {
    const ke = strEnd(raw, p);
    const k = JSON.parse(raw.slice(p, ke)) as string;
    p = ke;
    ws();
    p += 1; // ':'
    ws();
    return k;
  };
  ws();
  p += 1; // '['
  ws();
  while (raw.charCodeAt(p) !== 93) {
    p += 1; // '{' of the case object
    let ts = -1;
    let te = -1;
    let header = false;
    ws();
    while (raw.charCodeAt(p) !== 125) {
      const k = key();
      if (k === 'input') {
        p += 1; // '{' of the input object
        ws();
        while (raw.charCodeAt(p) !== 125) {
          const ik = key();
          if (ik === 'text') { ts = p; te = strEnd(raw, p); p = te; }
          else if (ik === 'header') { header = raw.charCodeAt(p) === 116; skipValue(); } // 't': only `true` starts with t
          else skipValue();
          ws();
          if (raw.charCodeAt(p) === 44) { p += 1; ws(); }
        }
        p += 1; // '}' of input
      } else skipValue();
      ws();
      if (raw.charCodeAt(p) === 44) { p += 1; ws(); }
    }
    p += 1; // '}' of the case
    starts.push(ts);
    ends.push(te);
    headers.push(header);
    ws();
    if (raw.charCodeAt(p) === 44) { p += 1; ws(); }
  }
  return { starts, ends, headers };
}

// --- span serializer ---------------------------------------------------------------

/** Append one answer's JSON (bare run() value) to out, straight from spans over text. */
export function serializeAnswer(text: string, ans: Answer, out: string[]): void {
  // Dirty character positions, once per text. Columns and rows emit spans in ascending text
  // order, so a single forward cursor over this list decides cleanliness in amortized O(1);
  // errors' extra spans are ascending too, but the cursor restarts for them.
  const dirty: number[] = [];
  let m: RegExpExecArray | null;
  while ((m = dirtyRe.exec(text)) !== null) dirty.push(m.index);
  let dPtr = 0;
  const field = (f: Field) => {
    if (typeof f === 'number') {
      const s = (f / MUL) | 0;
      const e = f - s * MUL;
      while (dPtr < dirty.length && dirty[dPtr] < s) dPtr += 1;
      if (dPtr >= dirty.length || dirty[dPtr] >= e) { out.push('"' + text.slice(s, e) + '"'); return; }
      out.push('"' + esc(text.slice(s, e)) + '"');
      return;
    }
    out.push('"' + esc(f) + '"');
  };
  const list = (fs: Field[]) => {
    out.push('[');
    for (let i = 0; i < fs.length; i += 1) {
      if (i > 0) out.push(',');
      field(fs[i]);
    }
    out.push(']');
  };
  out.push('{"columns":');
  if (ans.columns === null) out.push('null');
  else list(ans.columns);
  out.push(',"rows":[');
  for (let r = 0; r < ans.rows.length; r += 1) {
    if (r > 0) out.push(',');
    list(ans.rows[r]);
  }
  out.push('],"errors":[');
  dPtr = 0;
  for (let i = 0; i < ans.errors.length; i += 1) {
    if (i > 0) out.push(',');
    const e = ans.errors[i];
    out.push('{"code":"' + e.code + '","line":' + e.line + ',"row":' + (e.row === null ? 'null' : e.row));
    if (e.fields !== undefined) out.push(',"fields":' + e.fields);
    if (e.extra !== undefined) {
      out.push(',"extra":');
      list(e.extra);
    }
    out.push('}');
  }
  out.push(']}');
}

// --- pipeline ----------------------------------------------------------------------

export interface Timings {
  out: string;
  env: number;
  tok: number;
  parse: number;
  ser: number;
  join: number;
  total: number;
}

/** The whole v2 pipeline over raw cases.json bytes: scan, token-decode, span-parse, serialize. */
export function pipeline(raw: string): Timings {
  const t0 = performance.now();
  const env = scanEnvelope(raw);
  const t1 = performance.now();
  const n = env.starts.length;
  const texts: string[] = new Array(n);
  for (let i = 0; i < n; i += 1) texts[i] = JSON.parse(raw.slice(env.starts[i], env.ends[i])) as string;
  const t2 = performance.now();
  const parts: string[] = ['['];
  let parse = 0;
  let ser = 0;
  for (let i = 0; i < n; i += 1) {
    if (i > 0) parts.push(',');
    const a = performance.now();
    const ans = spans(texts[i], env.headers[i]);
    const b = performance.now();
    serializeAnswer(texts[i], ans, parts);
    const c = performance.now();
    parse += b - a;
    ser += c - b;
  }
  const t3 = performance.now();
  parts.push(']');
  const out = parts.join('');
  const t4 = performance.now();
  tEnv = t1 - t0;
  tTok = t2 - t1;
  tParse = parse;
  tSer = ser;
  return { out, env: tEnv, tok: tTok, parse, ser, join: t4 - t3, total: t4 - t0 };
}

const raw = readFileSync(join(INPUT_DIR, 'cases.json'), 'utf8');
const t = pipeline(raw);
writeFileSync(join(OUTPUT_DIR, 'answers.json'), t.out);
if (BENCH) {
  console.error(
    `env=${t.env.toFixed(3)} tok=${t.tok.toFixed(3)} parse=${t.parse.toFixed(3)} ser=${t.ser.toFixed(3)} join=${t.join.toFixed(3)} total=${t.total.toFixed(3)}`,
  );
}