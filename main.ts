// csv-reader 1.0.0 fast drop-in, v3 driver: raw Buffer in, answers Buffer out.
// cases.json is read as bytes and handed to solve.js's runCasesBuffer: no JSON.parse,
// no JSON.stringify, no TextDecoder anywhere in the hot path. Output shape is unchanged:
// a JSON array of BARE run() values in case order. CSV_V3_BENCH=1 prints total ms to stderr.

import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { setFlagsFromString } from 'node:v8';

// V8's incremental marking off, set before solve.js is imported so all of its work runs under it.
setFlagsFromString('--no-incremental-marking');

const { runCasesBuffer } = (await import(new URL('./solve.js', import.meta.url).href)) as {
  runCasesBuffer: (buf: Buffer) => Buffer;
};

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const BENCH = process.env.CSV_V3_BENCH === '1';
const t0 = performance.now();
const buf = readFileSync(join(INPUT_DIR, 'cases.json'));
const out = runCasesBuffer(buf);
writeFileSync(join(OUTPUT_DIR, 'answers.json'), out);
if (BENCH) {
  console.error(`total=${(performance.now() - t0).toFixed(3)}`);
}
