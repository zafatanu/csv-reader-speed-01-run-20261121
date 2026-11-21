// Fast drop-in for make.fun's csv-reader 1.0.0: same broken-row policy, index-based UTF-16 scanner.
// Native indexOf() for delimiter discovery, lazy slice() for field values, quote-reduction and
// newline normalization only on fields that need them. Pure: nothing kept from one call to the next.

const COMMA = 0;
const LINE_BREAK = 1;
const END = 2;

export function run(input) {
  const text = String(input.text);
  const header = input.header === true;
  const len = text.length;
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

  // Assemble a field value from a prefix, optional stray-CR-split parts, and the final [s, e) run.
  function assemble(prefix, parts, s, e) {
    const tail = s < e ? text.slice(s, e) : '';
    if (parts === null) return prefix === '' ? tail : prefix + tail;
    if (tail !== '') parts.push(tail);
    const joined = parts.join('');
    return prefix === '' ? joined : prefix + joined;
  }

  // Unquoted read from pos: a CR not followed by LF is dropped (stray_cr). Sets fValue/fEnded/fAdded.
  function readUnquoted(prefix) {
    let s = pos;
    let added = 0;
    let parts = null;
    while (pos < len) {
      const c = text.charCodeAt(pos);
      if (c === 44) {
        fValue = assemble(prefix, parts, s, pos);
        pos += 1;
        fEnded = COMMA;
        fAdded = added;
        return;
      }
      if (c === 10) {
        fValue = assemble(prefix, parts, s, pos);
        pos += 1;
        line += 1;
        fEnded = LINE_BREAK;
        fAdded = added;
        return;
      }
      if (c === 13) {
        if (text.charCodeAt(pos + 1) === 10) {
          fValue = assemble(prefix, parts, s, pos);
          pos += 2;
          line += 1;
          fEnded = LINE_BREAK;
          fAdded = added;
          return;
        }
        errors.push({ code: 'stray_cr', line: recordLine, row: recordRow });
        if (parts === null) parts = [];
        if (pos > s) parts.push(text.slice(s, pos));
        pos += 1;
        s = pos;
        continue;
      }
      added += 1;
      pos += 1;
    }
    fValue = assemble(prefix, parts, s, pos);
    fEnded = END;
    fAdded = added;
  }

  // Value of the quoted segment [s, e): count its lines, normalize CRLF/lone CR to LF only if a CR is present.
  function segValue(s, e) {
    if (s >= e) return '';
    const cr = text.indexOf('\r', s);
    if (cr < 0 || cr >= e) {
      let nl = text.indexOf('\n', s);
      while (nl >= 0 && nl < e) {
        line += 1;
        nl = text.indexOf('\n', nl + 1);
      }
      return text.slice(s, e);
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
        if (parts === null) parts = [sv, '"'];
        else parts.push(sv, '"');
        s = q + 2;
        q = text.indexOf('"', s);
        continue;
      }
      const sv = segValue(s, q);
      if (parts === null) fValue = sv;
      else {
        parts.push(sv);
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
