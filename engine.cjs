// sitegen-apex v4: Zero-Copy Para + Irregexp Markdown, Folded ConsString JIT Templates,
// Per-Post Card Cache, Single-utf8Write-per-case OutSlab & CJS Hyper-Fusion.

const { openSync, closeSync, readFileSync, writeSync } = require('node:fs');

let OUT_SLAB = Buffer.allocUnsafe(4 * 1024 * 1024);

function ensureSlab(need) {
  if (need <= OUT_SLAB.length) return;
  let cap = OUT_SLAB.length;
  while (cap < need) cap *= 2;
  OUT_SLAB = Buffer.allocUnsafe(cap);
}

// ---------------------------------------------------------------------------
// Escape helpers (pre-JSON-escaped HTML and JSON-only)
// ---------------------------------------------------------------------------
const HJ_TEST_RE = /[&<>"'\\\x00-\x1f]/;
const HJ_REPL_RE = /[&<>"'\\\x00-\x1f]/g;
const JSON_TEST_RE = /["\\\x00-\x1f]/;
const JSON_REPL_RE = /["\\\x00-\x1f]/g;

const HJ_CTRL = new Array(32);
for (let i = 0; i < 32; i++) HJ_CTRL[i] = '\\u00' + i.toString(16).padStart(2, '0');
HJ_CTRL[8] = '\\b'; HJ_CTRL[9] = '\\t'; HJ_CTRL[10] = '\\n'; HJ_CTRL[12] = '\\f'; HJ_CTRL[13] = '\\r';

const HJ_MAP = {
  '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
  '\\': '\\\\', '\n': '\\n', '\r': '\\r', '\t': '\\t', '\b': '\\b', '\f': '\\f',
};
for (let i = 0; i < 32; i++) {
  const ch = String.fromCharCode(i);
  if (!Object.hasOwn(HJ_MAP, ch)) HJ_MAP[ch] = HJ_CTRL[i];
}
const JSON_MAP = { ...HJ_MAP, '"': '\\"' };
delete JSON_MAP['&']; delete JSON_MAP['<']; delete JSON_MAP['>']; delete JSON_MAP["'"];
const hjFn = (c) => HJ_MAP[c];
const jsonFn = (c) => JSON_MAP[c];

function escHtmlJson(str) {
  if (str === '' || !HJ_TEST_RE.test(str)) return str;
  return str.replace(HJ_REPL_RE, hjFn);
}

function escJsonOnly(str) {
  if (str === '' || !JSON_TEST_RE.test(str)) return str;
  return str.replace(JSON_REPL_RE, jsonFn);
}

function escHtmlPlain(str) {
  return str.replace(/[&<>"']/g, hjFn);
}

// ---------------------------------------------------------------------------
// Text helpers: slugify (ASCII fast-path), uniqueSlug, longDate, wordsOf
// ---------------------------------------------------------------------------
const SLUG_MAX = 64;
const byCodeUnits = (a, b) => (a < b ? -1 : a > b ? 1 : 0);
const MONTHS = ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December'];
const RESERVED = Object.freeze(['posts', 'tags', 'page']);

const SLUG_TBL = new Uint8Array(128);
for (let c = 48; c <= 57; c++) SLUG_TBL[c] = c;
for (let c = 65; c <= 90; c++) SLUG_TBL[c] = c + 32;
for (let c = 97; c <= 122; c++) SLUG_TBL[c] = c;

const WS_TBL = new Uint8Array(128);
WS_TBL[9] = 1; WS_TBL[10] = 1; WS_TBL[11] = 1; WS_TBL[12] = 1; WS_TBL[13] = 1; WS_TBL[32] = 1;

function slugify(text) {
  const n = text.length;
  for (let i = 0; i < n; i++) {
    if (text.charCodeAt(i) >= 128) return slugifyUnicode(text);
  }
  let out = '';
  let gap = false;
  for (let i = 0; i < n; i++) {
    const mapped = SLUG_TBL[text.charCodeAt(i)];
    if (mapped === 0) {
      gap = out.length > 0;
      continue;
    }
    if (gap) {
      if (out.length === SLUG_MAX) break;
      out += '-';
      gap = false;
      if (out.length === SLUG_MAX) break;
    }
    out += String.fromCharCode(mapped);
    if (out.length === SLUG_MAX) break;
  }
  while (out.endsWith('-')) out = out.slice(0, -1);
  return out === '' ? 'untitled' : out;
}

function slugifyUnicode(text) {
  const plain = text.normalize('NFKD').replace(/\p{M}/gu, '');
  let out = '';
  let gap = false;
  for (const ch of plain) {
    let keep = null;
    if (ch >= 'A' && ch <= 'Z') keep = ch.toLowerCase();
    else if ((ch >= 'a' && ch <= 'z') || (ch >= '0' && ch <= '9')) keep = ch;
    if (keep === null) {
      gap = out.length > 0;
      continue;
    }
    if (gap) out += '-';
    gap = false;
    out += keep;
  }
  out = out.slice(0, SLUG_MAX).replace(/-+$/, '');
  return out === '' ? 'untitled' : out;
}

function uniqueSlug(slug, taken) {
  let out = slug;
  for (let n = 2; taken.has(out); n++) out = `${slug}-${n}`;
  taken.add(out);
  return out;
}

function longDate(date) {
  return `${Number(date.slice(8, 10))} ${MONTHS[Number(date.slice(5, 7)) - 1]} ${date.slice(0, 4)}`;
}

function textOf(v) {
  if (typeof v === 'string') return v;
  if (typeof v === 'number') return String(v);
  if (typeof v === 'boolean') return v ? 'true' : 'false';
  if (Array.isArray(v)) return v.map(textOf).join(', ');
  return '';
}

function truthy(v) {
  if (Array.isArray(v)) return v.length > 0;
  return v !== undefined && v !== null && v !== false && v !== '' && v !== 0;
}

function isUnicodeWsCode(c) {
  if (c < 128) return WS_TBL[c] === 1;
  if (c < 160) return false;
  return c === 0x00A0 || c === 0x1680 || (c >= 0x2000 && c <= 0x200A) || c === 0x2028 || c === 0x2029 || c === 0x202F || c === 0x205F || c === 0x3000 || c === 0xFEFF;
}

function wordsOf(text) {
  let words = 0;
  let inW = false;
  const n = text.length;
  for (let i = 0; i < n; i++) {
    const c = text.charCodeAt(i);
    if (c < 128) {
      if (WS_TBL[c] === 0) { if (!inW) { words++; inW = true; } }
      else inW = false;
    } else if (!isUnicodeWsCode(c)) {
      if (!inW) { words++; inW = true; }
    } else {
      inW = false;
    }
  }
  return words;
}

// ---------------------------------------------------------------------------
// Zero-split Frontmatter parser
// ---------------------------------------------------------------------------
const KEYS = ['title', 'date', 'tags', 'draft', 'layout', 'slug', 'summary'];
const DATE_RE = /^(\d{4})-(\d{2})-(\d{2})$/;
const NAME_RE = /^[a-z0-9-]+$/;
const SLUG_RE = /^[a-z0-9]+(?:-[a-z0-9]+)*$/;
const TAG_RE = /^[^"[\]]+$/;

function daysIn(y, m) {
  if (m === 2) return (y % 4 === 0 && y % 100 !== 0) || y % 400 === 0 ? 29 : 28;
  return m === 4 || m === 6 || m === 9 || m === 11 ? 30 : 31;
}

function stringOfFm(raw) {
  if (raw.charCodeAt(0) === 34) {
    if (raw.length < 2 || raw.charCodeAt(raw.length - 1) !== 34) return { error: 'a quoted string is not closed' };
    if (raw.indexOf('\\', 1) === -1 && raw.indexOf('"', 1) === raw.length - 1) {
      return { value: raw.slice(1, -1) };
    }
    let out = '';
    for (let i = 1; i < raw.length - 1; i++) {
      const c = raw[i];
      if (c === '\\') {
        const n = raw[i + 1];
        if ((n !== '"' && n !== '\\') || i + 1 === raw.length - 1) {
          return { error: 'a quoted string holds an escape other than \\" or \\\\' };
        }
        out += n;
        i++;
      } else if (c === '"') return { error: 'a quoted string holds a stray quote' };
      else out += c;
    }
    return { value: out };
  }
  if (raw.charCodeAt(0) === 91) return { error: 'a bare string opens on [' };
  return { value: raw };
}

function fmValueOf(key, raw) {
  switch (key) {
    case 'title':
    case 'summary': {
      const s = stringOfFm(raw);
      return 'error' in s ? { error: `key "${key}": ${s.error}` } : s;
    }
    case 'date': {
      const m = DATE_RE.exec(raw);
      const y = m ? Number(m[1]) : 0;
      const mo = m ? Number(m[2]) : 0;
      const d = m ? Number(m[3]) : 0;
      if (!m || y < 1970 || y > 2099 || mo < 1 || mo > 12 || d < 1 || d > daysIn(y, mo)) {
        return { error: 'key "date": not a date from 1970-01-01 to 2099-12-31 (YYYY-MM-DD)' };
      }
      return { value: raw };
    }
    case 'tags': {
      if (!raw.startsWith('[') || !raw.endsWith(']')) return { error: 'key "tags": not a list [a, b]' };
      const inner = raw.slice(1, -1);
      if (inner.trim() === '') return { value: [] };
      const tags = inner.split(',').map((t) => t.trim());
      if (tags.some((t) => t === '' || !TAG_RE.test(t))) return { error: 'key "tags": an empty tag, or one holding " [ or ]' };
      return { value: tags };
    }
    case 'draft':
      return raw === 'true' ? { value: true } : raw === 'false' ? { value: false } : { error: 'key "draft": true or false' };
    case 'layout':
      return NAME_RE.test(raw) ? { value: raw } : { error: 'key "layout": not a template name' };
    case 'slug':
      return SLUG_RE.test(raw) && raw.length <= 64 ? { value: raw } : { error: 'key "slug": not a slug' };
    default:
      return { error: `unknown key "${key}"` };
  }
}

function parseFrontMatterFast(text) {
  const len = text.length;
  let nl = text.indexOf('\n');
  let lEnd = nl === -1 ? len : nl;
  if (lEnd !== 3 || text.charCodeAt(0) !== 45 || text.charCodeAt(1) !== 45 || text.charCodeAt(2) !== 45) {
    return { error: 'no front matter' };
  }
  let pos = nl === -1 ? len + 1 : nl + 1;
  let closePos = -1;
  let bodyStart = len;
  while (pos < len) {
    nl = text.indexOf('\n', pos);
    lEnd = nl === -1 ? len : nl;
    if (lEnd - pos === 3 && text.charCodeAt(pos) === 45 && text.charCodeAt(pos + 1) === 45 && text.charCodeAt(pos + 2) === 45) {
      closePos = pos;
      bodyStart = nl === -1 ? len : nl + 1;
      break;
    }
    pos = nl === -1 ? len + 1 : nl + 1;
  }
  if (closePos === -1) return { error: 'the front matter is not closed' };

  const data = {};
  pos = text.indexOf('\n') + 1;
  let idx = 1;
  while (pos < closePos) {
    nl = text.indexOf('\n', pos);
    lEnd = nl === -1 || nl > closePos ? closePos : nl;
    let blank = true;
    for (let k = pos; k < lEnd; k++) {
      const c = text.charCodeAt(k);
      if (c !== 32 && c !== 9) { blank = false; break; }
    }
    if (!blank && text.charCodeAt(pos) !== 35) {
      const colon = text.indexOf(':', pos);
      if (colon === -1 || colon >= lEnd || colon === pos) {
        return { error: `line ${idx + 1} is not "key: value"` };
      }
      let validKey = true;
      for (let k = pos; k < colon; k++) {
        const b = text.charCodeAt(k);
        if (!((b >= 97 && b <= 122) || b === 95)) { validKey = false; break; }
      }
      if (!validKey || (colon + 1 < lEnd && text.charCodeAt(colon + 1) !== 32)) {
        return { error: `line ${idx + 1} is not "key: value"` };
      }
      let vs = colon + 2;
      let ve = lEnd;
      while (ve > vs && (text.charCodeAt(ve - 1) === 32 || text.charCodeAt(ve - 1) === 9)) ve--;
      const key = text.slice(pos, colon);
      if (!KEYS.includes(key)) return { error: `unknown key "${key}"` };
      if (Object.hasOwn(data, key)) return { error: `key "${key}" is given twice` };
      if (vs >= ve) return { error: `key "${key}" has no value` };

      if (key === 'draft') {
        const raw = text.slice(vs, ve);
        if (raw === 'true') data.draft = true;
        else if (raw === 'false') data.draft = false;
        else return { error: 'key "draft": true or false' };
      } else if ((key === 'title' || key === 'summary') && text.charCodeAt(vs) !== 34 && text.charCodeAt(vs) !== 91) {
        data[key] = text.slice(vs, ve);
      } else {
        const v = fmValueOf(key, text.slice(vs, ve));
        if ('error' in v) return v;
        data[key] = v.value;
      }
    }
    idx++;
    pos = lEnd + 1;
  }
  if (!Object.hasOwn(data, 'title')) return { error: 'no title' };
  return { data, body: bodyStart >= len ? '' : text.slice(bodyStart) };
}

// ---------------------------------------------------------------------------
// Zero-Copy Para + Zero-Alloc Irregexp Markdown Engine
// ---------------------------------------------------------------------------
const MD_RE = /[&<>"'\\`*\[\x00-\x1f]/g;
const ESCAPABLE_CC = new Uint8Array(128);
for (const ch of '\\`*_[]()#+-!>.') ESCAPABLE_CC[ch.charCodeAt(0)] = 1;
const LANG_CC = new Uint8Array(128);
for (let c = 48; c <= 57; c++) LANG_CC[c] = 1;
for (let c = 65; c <= 90; c++) LANG_CC[c] = 1;
for (let c = 97; c <= 122; c++) LANG_CC[c] = 1;
LANG_CC[95] = 1; LANG_CC[43] = 1; LANG_CC[45] = 1;

const SCHEME_F = new Uint8Array(128);
const SCHEME_R = new Uint8Array(128);
for (let c = 65; c <= 90; c++) { SCHEME_F[c] = 1; SCHEME_R[c] = 1; }
for (let c = 97; c <= 122; c++) { SCHEME_F[c] = 1; SCHEME_R[c] = 1; }
for (let c = 48; c <= 57; c++) SCHEME_R[c] = 1;
SCHEME_R[43] = 1; SCHEME_R[45] = 1; SCHEME_R[46] = 1;

// First-char table for lines that COULD possibly end a paragraph (space, tab, #, *, -, `)
const MAY_END_PARA = new Uint8Array(128);
MAY_END_PARA[9] = 1; MAY_END_PARA[32] = 1; MAY_END_PARA[35] = 1;
MAY_END_PARA[42] = 1; MAY_END_PARA[45] = 1; MAY_END_PARA[96] = 1;

function isSchemeFast(s, a, b) {
  if (a >= b) return false;
  const c0 = s.charCodeAt(a);
  if (c0 >= 128 || SCHEME_F[c0] === 0) return false;
  for (let i = a + 1; i < b; i++) {
    const c = s.charCodeAt(i);
    if (c === 58) return true;
    if (c >= 128 || SCHEME_R[c] === 0) return false;
  }
  return false;
}

function hasStrWhitespace(s, a, b) {
  for (let i = a; i < b; i++) if (isUnicodeWsCode(s.charCodeAt(i))) return true;
  return false;
}

function findUnescapedCharStr(s, targetCode, from, end) {
  for (let j = from; j < end; j++) {
    const c = s.charCodeAt(j);
    if (c === 92 && j + 1 < end) {
      const n = s.charCodeAt(j + 1);
      if (n < 128 && ESCAPABLE_CC[n] === 1) { j++; continue; }
    }
    if (c === targetCode) return j;
  }
  return -1;
}

function findUnescapedDStarStr(s, from, end) {
  const lim = end - 1;
  for (let j = from; j < lim; j++) {
    const c = s.charCodeAt(j);
    if (c === 92 && j + 1 < end) {
      const n = s.charCodeAt(j + 1);
      if (n < 128 && ESCAPABLE_CC[n] === 1) { j++; continue; }
    }
    if (c === 42 && s.charCodeAt(j + 1) === 42) return j;
  }
  return -1;
}

function findSingleStarStr(s, from, end) {
  for (let j = from; j < end; j++) {
    const c = s.charCodeAt(j);
    if (c === 92 && j + 1 < end) {
      const n = s.charCodeAt(j + 1);
      if (n < 128 && ESCAPABLE_CC[n] === 1) { j++; continue; }
    }
    if (c !== 42) continue;
    if (j + 1 < end && s.charCodeAt(j + 1) === 42) { j++; continue; }
    return j;
  }
  return -1;
}

function hjCharByCode(ch) {
  switch (ch) {
    case 38: return '&amp;';
    case 60: return '&lt;';
    case 62: return '&gt;';
    case 34: return '&quot;';
    case 39: return '&#39;';
    case 10: return '\\n';
    case 92: return '\\\\';
    case 13: return '\\r';
    case 9: return '\\t';
    case 8: return '\\b';
    case 12: return '\\f';
    default: return HJ_CTRL[ch];
  }
}

function inlineStr(s, linkFn) {
  const len = s.length;
  let out = '';
  let i = 0;
  while (i < len) {
    MD_RE.lastIndex = i;
    if (!MD_RE.test(s)) {
      return i === 0 ? s : out + s.slice(i);
    }
    const idx = MD_RE.lastIndex - 1;
    if (idx > i) out += s.slice(i, idx);
    const ch = s.charCodeAt(idx);
    if (ch !== 92 && ch !== 96 && ch !== 42 && ch !== 91) {
      out += hjCharByCode(ch);
      i = idx + 1;
      continue;
    }
    if (ch === 92) {
      if (idx + 1 < len) {
        const nc = s.charCodeAt(idx + 1);
        if (nc < 128 && ESCAPABLE_CC[nc] === 1) {
          out += nc === 62 ? '&gt;' : nc === 92 ? '\\\\' : s[idx + 1];
          i = idx + 2;
          continue;
        }
      }
      out += '\\\\';
      i = idx + 1;
      continue;
    }
    if (ch === 96) {
      const j = s.indexOf('`', idx + 1);
      if (j > idx + 1) {
        out += '<code>' + escHtmlJson(s.slice(idx + 1, j)) + '</code>';
        i = j + 1;
      } else {
        out += '`';
        i = idx + 1;
      }
      continue;
    }
    if (ch === 42) {
      if (s.charCodeAt(idx + 1) === 42) {
        const j = findUnescapedDStarStr(s, idx + 2, len);
        if (j > idx + 2) {
          out += '<strong>' + inlineStr(s.slice(idx + 2, j), linkFn) + '</strong>';
          i = j + 2;
        } else {
          out += '**';
          i = idx + 2;
        }
      } else {
        const j = findSingleStarStr(s, idx + 1, len);
        if (j > idx + 1) {
          out += '<em>' + inlineStr(s.slice(idx + 1, j), linkFn) + '</em>';
          i = j + 1;
        } else {
          out += '*';
          i = idx + 1;
        }
      }
      continue;
    }
    // ch === 91 '['
    const k = findUnescapedCharStr(s, 93, idx + 1, len);
    if (k !== -1 && k + 1 < len && s.charCodeAt(k + 1) === 40) {
      const m = s.indexOf(')', k + 2);
      if (m > k + 2 && !hasStrWhitespace(s, k + 2, m)) {
        const cFirst = s.charCodeAt(k + 2);
        const targetRaw = s.slice(k + 2, m);
        const hrefEsc = (cFirst === 47 || cFirst === 35 || isSchemeFast(s, k + 2, m))
          ? escHtmlJson(targetRaw)
          : escHtmlJson(linkFn(targetRaw));
        out += '<a href=\\"' + hrefEsc + '\\">' + inlineStr(s.slice(idx + 1, k), linkFn) + '</a>';
        i = m + 1;
        continue;
      }
    }
    out += '[';
    i = idx + 1;
  }
  return out;
}

function strIsBlank(src, s, e) {
  for (let i = s; i < e; i++) {
    const c = src.charCodeAt(i);
    if (c !== 32 && c !== 9) return false;
  }
  return true;
}

function strFenceOpen(src, s, e) {
  if (e - s < 3 || src.charCodeAt(s) !== 96 || src.charCodeAt(s + 1) !== 96 || src.charCodeAt(s + 2) !== 96) return -1;
  let i = s + 3;
  while (i < e) {
    const c = src.charCodeAt(i);
    if (c >= 128 || LANG_CC[c] === 0) break;
    i++;
  }
  const langEnd = i;
  while (i < e) {
    const c = src.charCodeAt(i);
    if (c !== 32 && c !== 9) return -1;
    i++;
  }
  return langEnd;
}

function strFenceClose(src, s, e) {
  if (e - s < 3 || src.charCodeAt(s) !== 96 || src.charCodeAt(s + 1) !== 96 || src.charCodeAt(s + 2) !== 96) return false;
  for (let i = s + 3; i < e; i++) {
    const c = src.charCodeAt(i);
    if (c !== 32 && c !== 9) return false;
  }
  return true;
}

function strIsHr(src, s, e) {
  if (e - s < 3) return false;
  const c = src.charCodeAt(s);
  if ((c !== 45 && c !== 42) || src.charCodeAt(s + 1) !== c || src.charCodeAt(s + 2) !== c) return false;
  for (let i = s + 3; i < e; i++) {
    const b = src.charCodeAt(i);
    if (b !== 32 && b !== 9) return false;
  }
  return true;
}

let _hd = 0, _hs = 0, _he = 0;
function strHeading(src, s, e) {
  if (s >= e || src.charCodeAt(s) !== 35) return false;
  let d = 1;
  let i = s + 1;
  while (i < e && src.charCodeAt(i) === 35 && d < 7) { d++; i++; }
  if (d > 6 || i >= e || (src.charCodeAt(i) !== 32 && src.charCodeAt(i) !== 9)) return false;
  i++;
  while (i < e && (src.charCodeAt(i) === 32 || src.charCodeAt(i) === 9)) i++;
  let end = e;
  while (end > i && (src.charCodeAt(end - 1) === 32 || src.charCodeAt(end - 1) === 9)) end--;
  if (end <= i) return false;
  _hd = d; _hs = i; _he = end;
  return true;
}

function strEndsParaFast(src, s, e) {
  if (s >= e) return true;
  const c0 = src.charCodeAt(s);
  if (c0 < 128 && MAY_END_PARA[c0] === 0) return false;
  if (c0 === 32 || c0 === 9) return strIsBlank(src, s, e);
  if (c0 === 96) return strFenceOpen(src, s, e) !== -1;
  if (c0 === 35) return strHeading(src, s, e);
  return strIsHr(src, s, e);
}

function strMatchOrd(src, s, e) {
  if (s >= e) return -1;
  let i = s;
  let digits = 0;
  while (i < e) {
    const c = src.charCodeAt(i);
    if (c < 48 || c > 57) break;
    digits++;
    if (digits > 9) return -1;
    i++;
  }
  if (digits === 0 || i + 1 >= e || src.charCodeAt(i) !== 46 || src.charCodeAt(i + 1) !== 32) return -1;
  return i + 2;
}

function strIsContinued(src, s, e) {
  if (e - s < 3 || src.charCodeAt(s) !== 32 || src.charCodeAt(s + 1) !== 32) return false;
  let i = s + 2;
  while (i < e && src.charCodeAt(i) === 32) i++;
  if (i >= e) return false;
  return !isUnicodeWsCode(src.charCodeAt(i));
}

function trimStrSpan(src, s, e) {
  while (s < e && (src.charCodeAt(s) === 32 || src.charCodeAt(s) === 9)) s++;
  while (e > s && (src.charCodeAt(e - 1) === 32 || src.charCodeAt(e - 1) === 9)) e--;
  return src.slice(s, e);
}

const REUSABLE_IDS = new Set();

function renderMarkdownFast(src, linkFn) {
  const len = src.length;
  REUSABLE_IDS.clear();
  const toc = [];
  let html = '';
  let excerpt = null;
  let pos = 0;

  while (pos <= len) {
    if (pos === len && len > 0 && src.charCodeAt(len - 1) === 10) break;
    let nl = pos >= len ? -1 : src.indexOf('\n', pos);
    let lEnd = nl === -1 ? len : nl;
    const c0 = pos < lEnd ? src.charCodeAt(pos) : -1;

    if (c0 === -1) {
      if (pos >= len) break;
      pos = nl === -1 ? len + 1 : nl + 1;
      continue;
    }

    // Fast path for non-special starting chars! Cannot be blank/fence/heading/hr/quote/list!
    if (!(c0 === 32 || c0 === 9 || c0 === 96 || c0 === 35 || c0 === 45 || c0 === 42 || c0 === 62 || (c0 >= 48 && c0 <= 57))) {
      // Fall straight into Zero-Copy Para!
    } else {
      if ((c0 === 32 || c0 === 9) && strIsBlank(src, pos, lEnd)) {
        if (pos >= len) break;
        pos = nl === -1 ? len + 1 : nl + 1;
        continue;
      }
      if (c0 === 96) {
        const langEnd = strFenceOpen(src, pos, lEnd);
        if (langEnd !== -1) {
          const lang = langEnd > pos + 3 ? ` class=\\"language-${escHtmlJson(src.slice(pos + 3, langEnd))}\\"` : '';
          let codeOut = '<pre><code' + lang + '>';
          pos = nl === -1 ? len + 1 : nl + 1;
          while (pos <= len) {
            nl = pos >= len ? -1 : src.indexOf('\n', pos);
            lEnd = nl === -1 ? len : nl;
            if (strFenceClose(src, pos, lEnd)) {
              pos = nl === -1 ? len + 1 : nl + 1;
              break;
            }
            if (lEnd > pos) codeOut += escHtmlJson(src.slice(pos, lEnd));
            codeOut += '\\n';
            if (pos >= len) { pos = len + 1; break; }
            pos = nl === -1 ? len + 1 : nl + 1;
          }
          html += codeOut + '</code></pre>\\n';
          continue;
        }
      }
      if (c0 === 35 && strHeading(src, pos, lEnd)) {
        const depth = _hd;
        const text = src.slice(_hs, _he);
        const id = uniqueSlug(slugify(text), REUSABLE_IDS);
        const inl = inlineStr(text, linkFn);
        html += `<h${depth} id=\\"${id}\\">${inl}</h${depth}>\\n`;
        if (depth === 2 || depth === 3) toc.push({ level: depth, id, html: inl });
        if (pos >= len) break;
        pos = nl === -1 ? len + 1 : nl + 1;
        continue;
      }
      if ((c0 === 45 || c0 === 42) && strIsHr(src, pos, lEnd)) {
        html += '<hr>\\n';
        if (pos >= len) break;
        pos = nl === -1 ? len + 1 : nl + 1;
        continue;
      }
      if (c0 === 62) {
        let bqText = '';
        while (pos <= len) {
          if (pos === len && len > 0 && src.charCodeAt(len - 1) === 10) break;
          nl = pos >= len ? -1 : src.indexOf('\n', pos);
          lEnd = nl === -1 ? len : nl;
          if (pos >= lEnd || src.charCodeAt(pos) !== 62) break;
          let ts = pos + 1;
          if (ts < lEnd && src.charCodeAt(ts) === 32) ts++;
          const trimmed = trimStrSpan(src, ts, lEnd);
          if (trimmed !== '') bqText = bqText === '' ? trimmed : bqText + '\n' + trimmed;
          if (pos >= len) { pos = len + 1; break; }
          pos = nl === -1 ? len + 1 : nl + 1;
        }
        html += bqText === '' ? '<blockquote>\\n</blockquote>\\n' : `<blockquote>\\n<p>${inlineStr(bqText, linkFn)}</p>\\n</blockquote>\\n`;
        continue;
      }
      const isUl = pos + 1 < lEnd && (c0 === 45 || c0 === 42) && src.charCodeAt(pos + 1) === 32;
      const ordPay = isUl || c0 < 48 || c0 > 57 ? -1 : strMatchOrd(src, pos, lEnd);
      if (isUl || ordPay !== -1) {
        let startNum = 1;
        if (!isUl) startNum = Number(src.slice(pos, ordPay - 2));
        const tag = isUl ? 'ul' : 'ol';
        let listOut = (isUl || startNum === 1 ? `<${tag}>` : `<ol start=\\"${startNum}\\">`) + '\\n';
        let curItem = null;
        while (pos <= len) {
          if (pos === len && len > 0 && src.charCodeAt(len - 1) === 10) break;
          nl = pos >= len ? -1 : src.indexOf('\n', pos);
          lEnd = nl === -1 ? len : nl;
          let payS = -1;
          if (isUl) {
            if (pos + 1 < lEnd && (src.charCodeAt(pos) === 45 || src.charCodeAt(pos) === 42) && src.charCodeAt(pos + 1) === 32) payS = pos + 2;
          } else {
            payS = strMatchOrd(src, pos, lEnd);
          }
          if (payS !== -1) {
            if (curItem !== null) listOut += '<li>' + inlineStr(curItem, linkFn) + '</li>\\n';
            curItem = trimStrSpan(src, payS, lEnd);
          } else if (curItem !== null && strIsContinued(src, pos, lEnd)) {
            curItem += '\n' + trimStrSpan(src, pos, lEnd);
          } else {
            break;
          }
          if (pos >= len) { pos = len + 1; break; }
          pos = nl === -1 ? len + 1 : nl + 1;
        }
        if (curItem !== null) listOut += '<li>' + inlineStr(curItem, linkFn) + '</li>\\n';
        html += listOut + `</${tag}>\\n`;
        continue;
      }
    }

    // Zero-Copy Paragraph! Only split/trim lines if ANY line has leading/trailing space or tab!
    const paraStart = pos;
    let prevEnd = lEnd;
    const last0 = lEnd > pos ? src.charCodeAt(lEnd - 1) : 0;
    let dirty = c0 === 32 || c0 === 9 || last0 === 32 || last0 === 9;
    pos = nl === -1 ? len + 1 : nl + 1;

    while (pos <= len) {
      if (pos === len && len > 0 && src.charCodeAt(len - 1) === 10) break;
      nl = pos >= len ? -1 : src.indexOf('\n', pos);
      lEnd = nl === -1 ? len : nl;
      if (strEndsParaFast(src, pos, lEnd)) break;
      if (!dirty) {
        const fc = src.charCodeAt(pos);
        const lc = src.charCodeAt(lEnd - 1);
        if (fc === 32 || fc === 9 || lc === 32 || lc === 9) dirty = true;
      }
      prevEnd = lEnd;
      if (pos >= len) { pos = len + 1; break; }
      pos = nl === -1 ? len + 1 : nl + 1;
    }

    let paraText;
    if (!dirty) {
      paraText = src.slice(paraStart, prevEnd);
    } else {
      let p2 = paraStart;
      paraText = '';
      let first = true;
      while (p2 <= prevEnd) {
        const n2 = p2 >= prevEnd ? -1 : src.indexOf('\n', p2);
        const le2 = n2 === -1 || n2 > prevEnd ? prevEnd : n2;
        const piece = trimStrSpan(src, p2, le2);
        if (first) { paraText = piece; first = false; }
        else paraText += '\n' + piece;
        if (n2 === -1 || n2 >= prevEnd) break;
        p2 = n2 + 1;
      }
    }

    const inl = inlineStr(paraText, linkFn);
    if (excerpt === null) excerpt = inl;
    html += '<p>' + inl + '</p>\\n';
  }

  return { html, toc, excerpt: excerpt ?? '' };
}

// ---------------------------------------------------------------------------
// Template Parser, Static Include Flattener, Constant Folder & ConsString JIT
// ---------------------------------------------------------------------------
const PATH_RE = /^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/;
const FOR_RE = /^for ([A-Za-z_][A-Za-z0-9_]*) in (\S+)$/;
const IF_RE = /^if (not )?(\S+)$/;
const INCLUDE_RE = /^include "([a-z0-9-]+)"$/;
const INCLUDE_DEPTH = 8;

class TemplateError extends Error {}

function tplPathOf(name, text) {
  if (!PATH_RE.test(text)) throw new TemplateError(`template "${name}": ${JSON.stringify(text)} is not a path`);
  return text.split('.');
}

function tokenizeTemplate(name, src) {
  const tokens = [];
  let text = '';
  let i = 0;
  while (i < src.length) {
    const open = src.indexOf('{', i);
    if (open === -1 || open === src.length - 1) {
      text += src.slice(i);
      break;
    }
    const next = src[open + 1];
    if (next !== '{' && next !== '%') {
      text += src.slice(i, open + 1);
      i = open + 1;
      continue;
    }
    text += src.slice(i, open);
    if (next === '{') {
      const raw = src[open + 2] === '{';
      const close = src.indexOf(raw ? '}}}' : '}}', open + (raw ? 3 : 2));
      if (close === -1) throw new TemplateError(`template "${name}": a ${raw ? '{{{' : '{{'} is not closed`);
      if (text !== '') tokens.push({ t: 'text', text });
      text = '';
      tokens.push({ t: raw ? 'raw' : 'var', path: tplPathOf(name, src.slice(open + (raw ? 3 : 2), close).trim()) });
      i = close + (raw ? 3 : 2);
      continue;
    }
    const close = src.indexOf('%}', open + 2);
    if (close === -1) throw new TemplateError(`template "${name}": a {% is not closed`);
    const end = close + 2;
    const lineStart = src.lastIndexOf('\n', open - 1) + 1;
    const nl = src.indexOf('\n', end);
    const lineEnd = nl === -1 ? src.length : nl;
    const standalone = /^[ \t]*$/.test(src.slice(lineStart, open)) && /^[ \t]*$/.test(src.slice(end, lineEnd));
    if (standalone) text = text.slice(0, text.length - (open - lineStart));
    if (text !== '') tokens.push({ t: 'text', text });
    text = '';
    tokens.push({ t: 'tag', tag: src.slice(open + 2, close).trim() });
    i = standalone ? (nl === -1 ? src.length : nl + 1) : end;
  }
  if (text !== '') tokens.push({ t: 'text', text });
  return tokens;
}

function parseTemplateAst(name, src) {
  const root = { kind: 'root', body: [] };
  const stack = [root];
  let body = root.body;
  for (const tok of tokenizeTemplate(name, src)) {
    if (tok.t === 'text') body.push({ kind: 'text', text: tok.text });
    else if (tok.t === 'var' || tok.t === 'raw') body.push({ kind: tok.t, path: tok.path });
    else {
      const tag = tok.tag;
      const top = stack[stack.length - 1];
      let m;
      if ((m = FOR_RE.exec(tag)) !== null) {
        const node = { kind: 'for', name: m[1], path: tplPathOf(name, m[2]), body: [] };
        body.push(node);
        stack.push(node);
        body = node.body;
      } else if ((m = IF_RE.exec(tag)) !== null) {
        const node = { kind: 'if', not: m[1] !== undefined, path: tplPathOf(name, m[2]), then: [], else: null };
        body.push(node);
        stack.push(node);
        body = node.then;
      } else if (tag === 'else') {
        if (top.kind !== 'if' || top.else !== null) throw new TemplateError(`template "${name}": an else outside an if`);
        top.else = [];
        body = top.else;
      } else if (tag === 'endfor' || tag === 'endif') {
        if (top.kind !== (tag === 'endfor' ? 'for' : 'if')) throw new TemplateError(`template "${name}": an ${tag} with no open ${tag.slice(3)}`);
        stack.pop();
        const parent = stack[stack.length - 1];
        body = parent.kind === 'root' ? parent.body : parent.kind === 'for' ? parent.body : parent.else ?? parent.then;
      } else if ((m = INCLUDE_RE.exec(tag)) !== null) body.push({ kind: 'include', name: m[1] });
      else throw new TemplateError(`template "${name}": {% ${tag} %} is not a tag`);
    }
  }
  if (stack.length > 1) throw new TemplateError(`template "${name}": a ${stack[stack.length - 1].kind} is not closed`);
  return root.body;
}

function inlineAstIncludes(nodes, tplMap, depth) {
  const out = [];
  for (let i = 0; i < nodes.length; i++) {
    const n = nodes[i];
    if (n.kind === 'include') {
      const t = tplMap.get(n.name);
      if (t !== undefined && depth < INCLUDE_DEPTH) {
        const sub = inlineAstIncludes(t, tplMap, depth + 1);
        for (let j = 0; j < sub.length; j++) out.push(sub[j]);
      }
    } else if (n.kind === 'if') {
      out.push({
        kind: 'if', not: n.not, path: n.path,
        then: inlineAstIncludes(n.then, tplMap, depth),
        else: n.else === null ? null : inlineAstIncludes(n.else, tplMap, depth),
      });
    } else if (n.kind === 'for') {
      out.push({ kind: 'for', name: n.name, path: n.path, body: inlineAstIncludes(n.body, tplMap, depth) });
    } else {
      out.push(n);
    }
  }
  return out;
}

function freeVarsOfNodes(nodes, bound, outSet) {
  for (let i = 0; i < nodes.length; i++) {
    const n = nodes[i];
    if (n.kind === 'var' || n.kind === 'raw') {
      if (!bound.has(n.path[0])) outSet.add(n.path[0]);
    } else if (n.kind === 'if') {
      if (!bound.has(n.path[0])) outSet.add(n.path[0]);
      freeVarsOfNodes(n.then, bound, outSet);
      if (n.else !== null) freeVarsOfNodes(n.else, bound, outSet);
    } else if (n.kind === 'for') {
      if (!bound.has(n.path[0])) outSet.add(n.path[0]);
      const inner = new Set(bound);
      inner.add(n.name);
      inner.add('loop');
      freeVarsOfNodes(n.body, inner, outSet);
    }
  }
  return outSet;
}

const INVARIANT_ROOTS = new Set(['site', 'tags', 'recent']);
function isSiteInvariant(freeSet) {
  for (const v of freeSet) if (!INVARIANT_ROOTS.has(v)) return false;
  return true;
}

function lookupDynamic(scope, path) {
  let s = scope;
  while (s !== null && !Object.hasOwn(s.vars, path[0])) s = s.parent;
  if (s === null) return undefined;
  let v = s.vars[path[0]];
  for (let k = 1; k < path.length; k++) {
    if (v === null || typeof v !== 'object' || !Object.hasOwn(v, path[k])) return undefined;
    v = v[path[k]];
  }
  return v;
}

function renderDynamicPlain(nodes, scope) {
  let out = '';
  for (let i = 0; i < nodes.length; i++) {
    const n = nodes[i];
    switch (n.kind) {
      case 'text': out += n.text; break;
      case 'var': out += escHtmlPlain(textOf(lookupDynamic(scope, n.path))); break;
      case 'raw': out += textOf(lookupDynamic(scope, n.path)); break;
      case 'if': {
        const v = truthy(lookupDynamic(scope, n.path));
        const br = v !== n.not ? n.then : n.else;
        if (br !== null) out += renderDynamicPlain(br, scope);
        break;
      }
      case 'for': {
        const xs = lookupDynamic(scope, n.path);
        if (!Array.isArray(xs)) break;
        const len = xs.length;
        for (let k = 0; k < len; k++) {
          const vars = { [n.name]: xs[k], loop: { index: k + 1, first: k === 0, last: k === len - 1, length: len } };
          out += renderDynamicPlain(n.body, { vars, parent: scope });
        }
        break;
      }
    }
  }
  return out;
}

function foldInvariantNodes(nodes, siteScope) {
  const folded = [];
  const pushTxt = (txt) => {
    if (txt === '') return;
    if (folded.length > 0 && folded[folded.length - 1].kind === 'text') folded[folded.length - 1].text += txt;
    else folded.push({ kind: 'text', text: txt });
  };
  for (let i = 0; i < nodes.length; i++) {
    const n = nodes[i];
    if (n.kind === 'text') pushTxt(n.text);
    else if (n.kind === 'var' || n.kind === 'raw') {
      if (INVARIANT_ROOTS.has(n.path[0])) {
        const val = textOf(lookupDynamic(siteScope, n.path));
        pushTxt(n.kind === 'var' ? escHtmlPlain(val) : val);
      } else folded.push(n);
    } else if (n.kind === 'if') {
      if (INVARIANT_ROOTS.has(n.path[0])) {
        const v = truthy(lookupDynamic(siteScope, n.path));
        const br = v !== n.not ? n.then : n.else;
        if (br !== null) {
          for (const ch of foldInvariantNodes(br, siteScope)) {
            if (ch.kind === 'text') pushTxt(ch.text);
            else folded.push(ch);
          }
        }
      } else {
        folded.push({
          kind: 'if', not: n.not, path: n.path,
          then: foldInvariantNodes(n.then, siteScope),
          else: n.else === null ? null : foldInvariantNodes(n.else, siteScope),
        });
      }
    } else if (n.kind === 'for') {
      const fset = freeVarsOfNodes([n], new Set(), new Set());
      if (isSiteInvariant(fset)) {
        pushTxt(renderDynamicPlain([n], siteScope));
      } else {
        const bodyF = foldInvariantNodes(n.body, siteScope);
        const bodyFree = freeVarsOfNodes(bodyF, new Set(), new Set());
        bodyFree.delete(n.name);
        const pureCardLoop = (n.path.length === 1 && n.path[0] === 'posts') || (n.path.length === 2 && n.path[0] === 'tag' && n.path[1] === 'posts');
        folded.push({ kind: 'for', name: n.name, path: n.path, body: bodyF, cacheCards: pureCardLoop && bodyFree.size === 0 });
      }
    }
  }
  return folded;
}

const STRING_JIT_HELPERS = { lookup: lookupDynamic, textOf, truthy, escHJ: escHtmlJson, escJ: escJsonOnly };

function compileToConsFn(nodes, tplKind) {
  const chunks = [];
  const addChunk = (str) => {
    const idx = chunks.length;
    chunks.push(escJsonOnly(str));
    return `C[${idx}]`;
  };
  let varId = 0;
  let needsDynScope = false;

  function resolve(path, env) {
    const r = path[0];
    const bVar = env.get(r);
    if (bVar === undefined) {
      if (r === 'page' || r === 'posts' || r === 'pager' || r === 'tag') return { missing: true };
      return null;
    }
    if (bVar.kind === 'loop') {
      if (path.length === 1) return { alwaysTrue: true };
      if (path.length === 2) {
        const f = path[1];
        if (f === 'index') return { expr: `${bVar.v}_idx`, int: true, tru: `${bVar.v}_idx !== 0` };
        if (f === 'length') return { expr: `${bVar.v}_len`, int: true, tru: `${bVar.v}_len !== 0` };
        if (f === 'first') return { expr: `(${bVar.v}_idx === 1)`, bool: true, tru: `(${bVar.v}_idx === 1)` };
        if (f === 'last') return { expr: `(${bVar.v}_idx === ${bVar.v}_len)`, bool: true, tru: `(${bVar.v}_idx === ${bVar.v}_len)` };
      }
      return null;
    }
    if (bVar.kind === 'page' || bVar.kind === 'card') {
      if (path.length === 1) return { alwaysTrue: true };
      if (path.length === 2) {
        const f = path[1];
        if (f === 'title') return { esc: `${bVar.v}._jt`, tru: `${bVar.v}._jt !== ''` };
        if (f === 'url') return { esc: `${bVar.v}._ju`, tru: `${bVar.v}._ju !== ''` };
        if (f === 'date') return { esc: `${bVar.v}.date`, tru: `${bVar.v}.date !== ''` };
        if (f === 'date_long') return { esc: `${bVar.v}.date_long`, tru: `${bVar.v}.date_long !== ''` };
        if (f === 'summary') return { esc: `${bVar.v}._js`, tru: `${bVar.v}._js !== ''` };
        if (f === 'slug' && bVar.kind === 'page') return { esc: `${bVar.v}._jslug`, tru: `${bVar.v}._jslug !== ''` };
        if (f === 'excerpt') return { preJson: `${bVar.v}.excerpt`, tru: `${bVar.v}.excerpt !== ''` };
        if (f === 'content' && bVar.kind === 'page') return { preJson: `${bVar.v}.content`, tru: `${bVar.v}.content !== ''` };
        if (f === 'reading_minutes') return { expr: `${bVar.v}.reading_minutes`, int: true, tru: `${bVar.v}.reading_minutes !== 0` };
        if (f === 'is_post' && bVar.kind === 'page') return { expr: `${bVar.v}.is_post`, bool: true, tru: `${bVar.v}.is_post` };
        if (f === 'tags' || (bVar.kind === 'page' && f === 'toc')) return { arr: `${bVar.v}.${f}`, tru: `${bVar.v}.${f}.length > 0` };
        if (bVar.kind === 'page' && (f === 'newer' || f === 'older')) return { tru: `${bVar.v}.${f} !== null` };
      } else if (path.length === 3 && bVar.kind === 'page' && (path[1] === 'newer' || path[1] === 'older')) {
        const nb = path[1];
        const f = path[2];
        if (f === 'title') return { esc: `(${bVar.v}.${nb} ? ${bVar.v}.${nb}._jt : '')`, tru: `(${bVar.v}.${nb} !== null && ${bVar.v}.${nb}._jt !== '')` };
        if (f === 'url') return { esc: `(${bVar.v}.${nb} ? ${bVar.v}.${nb}._ju : '')`, tru: `(${bVar.v}.${nb} !== null && ${bVar.v}.${nb}._ju !== '')` };
        if (f === 'date') return { esc: `(${bVar.v}.${nb} ? ${bVar.v}.${nb}.date : '')`, tru: `(${bVar.v}.${nb} !== null && ${bVar.v}.${nb}.date !== '')` };
        if (f === 'date_long') return { esc: `(${bVar.v}.${nb} ? ${bVar.v}.${nb}.date_long : '')`, tru: `(${bVar.v}.${nb} !== null && ${bVar.v}.${nb}.date_long !== '')` };
      }
    }
    if (bVar.kind === 'tagObj' || bVar.kind === 'tagItem') {
      if (path.length === 1) return { alwaysTrue: true };
      if (path.length === 2) {
        const f = path[1];
        if (f === 'name') return { esc: `${bVar.v}._jn`, tru: `${bVar.v}._jn !== ''` };
        if (f === 'slug') return { esc: `${bVar.v}._jsl`, tru: `${bVar.v}._jsl !== ''` };
        if (f === 'url') return { esc: `${bVar.v}._ju`, tru: `${bVar.v}._ju !== ''` };
        if (f === 'count') return { expr: `${bVar.v}.count`, int: true, tru: `${bVar.v}.count !== 0` };
        if (f === 'posts' && bVar.kind === 'tagObj') return { arr: `${bVar.v}.posts`, tru: `${bVar.v}.posts.length > 0` };
      }
    }
    if (bVar.kind === 'tocItem') {
      if (path.length === 1) return { alwaysTrue: true };
      if (path.length === 2) {
        const f = path[1];
        if (f === 'level') return { expr: `${bVar.v}.level`, int: true, tru: `${bVar.v}.level !== 0` };
        if (f === 'id') return { esc: `${bVar.v}._jid`, tru: `${bVar.v}._jid !== ''` };
        if (f === 'html') return { preJson: `${bVar.v}.html`, tru: `${bVar.v}.html !== ''` };
      }
    }
    if (bVar.kind === 'pager') {
      if (path.length === 1) return { alwaysTrue: true };
      if (path.length === 2) {
        const f = path[1];
        if (f === 'number' || f === 'total') return { expr: `${bVar.v}.${f}`, int: true, tru: `${bVar.v}.${f} !== 0` };
        if (f === 'url') return { esc: `${bVar.v}._ju`, tru: `${bVar.v}._ju !== ''` };
        if (f === 'newer_url') return { esc: `${bVar.v}._jn`, tru: `${bVar.v}._jn !== ''` };
        if (f === 'older_url') return { esc: `${bVar.v}._jo`, tru: `${bVar.v}._jo !== ''` };
      }
    }
    if (bVar.kind === 'postsArr') {
      if (path.length === 1) return { arr: `${bVar.v}`, tru: `${bVar.v}.length > 0` };
    }
    return null;
  }

  // Emit inline JS expression pieces joined cleanly as `+` inside `_o += ...`!
  function genBlock(list, env, scName, outVar) {
    let code = '';
    let terms = [];
    const flushTerms = () => {
      if (terms.length > 0) {
        code += `  ${outVar} += ${terms.join(' + ')};\n`;
        terms = [];
      }
    };

    for (let i = 0; i < list.length; i++) {
      const n = list[i];
      if (n.kind === 'text') {
        if (n.text !== '') terms.push(addChunk(n.text));
      } else if (n.kind === 'var' || n.kind === 'raw') {
        const isRaw = n.kind === 'raw';
        const r = resolve(n.path, env);
        if (r && r.missing) continue;
        if (r && r.int) { terms.push(r.expr); continue; }
        if (r && r.bool) { terms.push(`(${r.expr} ? 'true' : 'false')`); continue; }
        if (r && !isRaw && r.esc) { terms.push(r.esc); continue; }
        if (r && isRaw && r.preJson) { terms.push(r.preJson); continue; }
        needsDynScope = true;
        const pStr = JSON.stringify(n.path);
        terms.push(isRaw ? `H.escJ(H.textOf(H.lookup(${scName}, ${pStr})))` : `H.escHJ(H.textOf(H.lookup(${scName}, ${pStr})))`);
      } else if (n.kind === 'if') {
        const r = resolve(n.path, env);
        if (r && r.missing) {
          const br = n.not ? n.then : n.else;
          if (br !== null) {
            flushTerms();
            code += genBlock(br, env, scName, outVar);
          }
          continue;
        }
        if (r && r.alwaysTrue) {
          const br = !n.not ? n.then : n.else;
          if (br !== null) {
            flushTerms();
            code += genBlock(br, env, scName, outVar);
          }
          continue;
        }
        flushTerms();
        let condExpr;
        if (r && r.tru) condExpr = n.not ? `!(${r.tru})` : r.tru;
        else {
          needsDynScope = true;
          condExpr = `${n.not ? '!' : ''}H.truthy(H.lookup(${scName}, ${JSON.stringify(n.path)}))`;
        }
        code += `  if (${condExpr}) {\n${genBlock(n.then, env, scName, outVar)}  }`;
        if (n.else !== null) code += ` else {\n${genBlock(n.else, env, scName, outVar)}  }`;
        code += '\n';
      } else if (n.kind === 'for') {
        const r = resolve(n.path, env);
        if (r && r.missing) continue;
        flushTerms();
        const id = varId++;
        const xs = `xs${id}`, item = `it${id}`, len = `${item}_len`, idx = `${item}_idx`, k = `k${id}`;
        let arrExpr;
        if (r && r.arr) arrExpr = r.arr;
        else {
          needsDynScope = true;
          arrExpr = `H.lookup(${scName}, ${JSON.stringify(n.path)})`;
        }
        let itemKind = 'unknown';
        if (n.path.length === 1 && (n.path[0] === 'posts' || n.path[0] === 'recent')) itemKind = 'card';
        else if (n.path.length === 1 && n.path[0] === 'tags') itemKind = 'tagItem';
        else if (n.path.length === 2 && n.path[0] === 'tag' && n.path[1] === 'posts') itemKind = 'card';
        else if (n.path.length === 2 && (n.path[0] === 'page' || (env.get(n.path[0])?.kind === 'card')) && n.path[1] === 'tags') itemKind = 'tagItem';
        else if (n.path.length === 2 && n.path[0] === 'page' && n.path[1] === 'toc') itemKind = 'tocItem';

        const nextEnv = new Map(env);
        nextEnv.set(n.name, { kind: itemKind, v: item });
        nextEnv.set('loop', { kind: 'loop', v: item });
        const innerSc = `sc${id}`;
        const prevNeeds = needsDynScope;
        const innerCode = genBlock(n.body, nextEnv, innerSc, n.cacheCards ? `co${id}` : outVar);
        const loopUsedDyn = needsDynScope && !prevNeeds; // approx conservative check: pass innerSc whenever needsDynScope!

        code += `  const ${xs} = ${arrExpr};\n  if (Array.isArray(${xs})) {\n    const ${len} = ${xs}.length;\n    for (let ${k} = 0; ${k} < ${len}; ${k}++) {\n      const ${item} = ${xs}[${k}];\n      const ${idx} = ${k} + 1;\n`;
        if (n.cacheCards && !needsDynScope) {
          code += `      const cid${id} = ${item}._cid;\n      let cs${id} = CC[cid${id}];\n      if (cs${id} === undefined) {\n        let co${id} = '';\n${innerCode}        cs${id} = CC[cid${id}] = co${id};\n      }\n      ${outVar} += cs${id};\n`;
        } else {
          if (needsDynScope) {
            code += `      const ${innerSc} = { vars: { ${JSON.stringify(n.name)}: ${item}, loop: { index: ${idx}, first: ${idx} === 1, last: ${idx} === ${len}, length: ${len} } }, parent: ${scName} };\n`;
          }
          // Wait: if cacheCards was true AND loop didn't use dyn before innerCode, we emitted `co${id}` yet took else branch if an earlier op needed dyn! Fix: always use `outVar` when !actuallyCached:
          if (n.cacheCards && needsDynScope) {
            code += `      let co${id} = '';\n${innerCode}      ${outVar} += co${id};\n`;
          } else {
            code += innerCode;
          }
        }
        code += `    }\n  }\n`;
      }
    }
    flushTerms();
    return code;
  }

  const rootEnv = new Map();
  if (tplKind === 'page') rootEnv.set('page', { kind: 'page', v: 'arg0' });
  else if (tplKind === 'index') {
    rootEnv.set('posts', { kind: 'postsArr', v: 'arg0' });
    rootEnv.set('pager', { kind: 'pager', v: 'arg1' });
  } else if (tplKind === 'tag') {
    rootEnv.set('tag', { kind: 'tagObj', v: 'arg0' });
  }

  const bodyCode = genBlock(nodes, rootEnv, 'baseSc', '_o');
  const fnCode = `return function(C, CC, H, baseSc, arg0, arg1) {\n  let _o = '';\n${bodyCode}  return _o;\n};\n`;
  const fn = new Function(fnCode)();
  return { fn, chunks, needsDynScope };
}

// ---------------------------------------------------------------------------
// Core site builder -> emits one JSON string `{...}` directly
// ---------------------------------------------------------------------------
function resolveRelPathParts(dirParts, rel) {
  const parts = dirParts.length === 0 ? [] : dirParts.slice();
  const segs = rel.split('/');
  for (let i = 0; i < segs.length; i++) {
    const seg = segs[i];
    if (seg === '' || seg === '.') continue;
    if (seg === '..') {
      if (parts.length === 0) return null;
      parts.pop();
    } else parts.push(seg);
  }
  return parts.join('/');
}

const dirOf = (path) => (path.includes('/') ? path.slice(0, path.lastIndexOf('/')) : '');

function buildSiteJsonStr(input) {
  const rawTpls = new Map();
  const report = [];
  const tplNames = Object.keys(input.templates).sort(byCodeUnits);
  for (let i = 0; i < tplNames.length; i++) {
    const name = tplNames[i];
    try {
      rawTpls.set(name, parseTemplateAst(name, input.templates[name]));
    } catch (err) {
      if (!(err instanceof TemplateError)) throw err;
      report.push(err.message);
    }
  }

  const mdSources = [];
  const statics = [];
  const rawFiles = input.files;
  for (let i = 0; i < rawFiles.length; i++) {
    const f = rawFiles[i];
    if (f.path.endsWith('.md')) mdSources.push(f);
    else statics.push(f);
  }
  mdSources.sort((a, b) => byCodeUnits(a.path, b.path));
  statics.sort((a, b) => byCodeUnits(a.path, b.path));

  const base = input.site.base_url.replace(/\/+$/, '');
  const siteVar = { title: input.site.title, base_url: base };

  const kept = [];
  for (let i = 0; i < mdSources.length; i++) {
    const src = mdSources[i];
    const rawC = src.content;
    const norm = rawC.indexOf('\r') === -1 ? rawC : rawC.replace(/\r\n?/g, '\n');
    const fm = parseFrontMatterFast(norm);
    if ('error' in fm) {
      report.push(`refused ${src.path}: ${fm.error}`);
      continue;
    }
    const post = src.path.startsWith('posts/');
    let ownReserved = null;
    if (!post) {
      if (src.path.startsWith('tags/')) ownReserved = 'tags';
      else if (src.path.startsWith('page/')) ownReserved = 'page';
    }
    if (ownReserved !== null) {
      report.push(`refused ${src.path}: ${ownReserved}/ is the generator's own`);
      continue;
    }
    if (post && !Object.hasOwn(fm.data, 'date')) {
      report.push(`refused ${src.path}: a post needs a date`);
      continue;
    }
    const layout = fm.data.layout ?? (post ? 'post' : 'page');
    if (!rawTpls.has(layout)) {
      report.push(`refused ${src.path}: layout "${layout}" is no template that parses`);
      continue;
    }
    if (fm.data.draft === true) {
      report.push(`draft ${src.path}`);
      continue;
    }
    kept.push({
      path: src.path, data: fm.data, body: fm.body, post, layout,
      slug: '', outDir: '', url: '', pageObj: null, newer: null, older: null, tagRefs: null,
    });
  }

  const takenMap = new Map();
  const bySource = new Map();
  const slugCache = new Map();
  const cachedSlug = (name) => {
    let sl = slugCache.get(name);
    if (sl === undefined) { sl = slugify(name); slugCache.set(name, sl); }
    return sl;
  };

  for (let i = 0; i < kept.length; i++) {
    const s = kept[i];
    const dir = s.post ? 'posts' : dirOf(s.path);
    let tSet = takenMap.get(dir);
    if (tSet === undefined) {
      tSet = new Set(dir === '' ? RESERVED : []);
      takenMap.set(dir, tSet);
    }
    const slug = uniqueSlug(s.data.slug ?? slugify(s.data.title), tSet);
    s.slug = slug;
    s.outDir = dir === '' ? slug : `${dir}/${slug}`;
    s.url = `${base}/${s.outDir}/`;
    bySource.set(s.path, s);
  }

  const staticPathSet = new Set();
  for (let i = 0; i < statics.length; i++) staticPathSet.add(statics[i].path);
  const broken = new Set();
  const dirPartsCache = new Map();

  for (let i = 0; i < kept.length; i++) {
    const s = kept[i];
    const dir = dirOf(s.path);
    let dirParts = dirPartsCache.get(dir);
    if (dirParts === undefined) {
      dirParts = dir === '' ? [] : dir.split('/');
      dirPartsCache.set(dir, dirParts);
    }
    const linkFn = (target) => {
      if (target[0] === '/' || target[0] === '#' || isSchemeFast(target, 0, target.length)) return target;
      const hash = target.indexOf('#');
      const rel = hash === -1 ? target : target.slice(0, hash);
      const frag = hash === -1 ? '' : target.slice(hash);
      const resolved = rel === '' ? null : resolveRelPathParts(dirParts, rel);
      if (resolved !== null) {
        const hit = bySource.get(resolved);
        if (hit !== undefined) return `${hit.url}${frag}`;
        if (staticPathSet.has(resolved)) return `${base}/${resolved}${frag}`;
      }
      broken.add(`broken-link ${s.path} -> ${target}`);
      return target;
    };
    s._md = renderMarkdownFast(s.body, linkFn);
    s._words = wordsOf(s.body);
  }

  const posts = kept.filter((s) => s.post);
  posts.sort((x, y) => byCodeUnits(y.data.date, x.data.date) || byCodeUnits(x.slug, y.slug));
  for (let k = 0; k < posts.length; k++) {
    posts[k].newer = k === 0 ? null : posts[k - 1];
    posts[k].older = k === posts.length - 1 ? null : posts[k + 1];
  }

  const byTagSlug = new Map();
  const ownTags = (s) => {
    const arr = s.data.tags;
    if (arr === undefined || arr.length === 0) return [];
    const seen = new Set();
    const res = [];
    for (let i = 0; i < arr.length; i++) {
      const name = arr[i];
      const sl = cachedSlug(name);
      if (!seen.has(sl)) { seen.add(sl); res.push([name, sl]); }
    }
    return res;
  };

  for (let i = 0; i < posts.length; i++) {
    const p = posts[i];
    const ot = ownTags(p);
    p.tagRefs = [];
    for (let k = 0; k < ot.length; k++) {
      const [name, sl] = ot[k];
      let tObj = byTagSlug.get(sl);
      if (tObj === undefined) {
        tObj = { name, slug: sl, url: `${base}/tags/${sl}/`, posts: [] };
        byTagSlug.set(sl, tObj);
      }
      tObj.posts.push(p);
      p.tagRefs.push(tObj);
    }
  }
  for (let i = 0; i < kept.length; i++) {
    const s = kept[i];
    if (!s.post) {
      const ot = ownTags(s);
      s.tagRefs = [];
      for (let k = 0; k < ot.length; k++) {
        const [name, sl] = ot[k];
        s.tagRefs.push(byTagSlug.get(sl) ?? { name, slug: sl, url: '', posts: [] });
      }
    }
  }
  const tagsList = [...byTagSlug.values()].sort((x, y) => y.posts.length - x.posts.length || byCodeUnits(x.slug, y.slug));

  const tagCards = new Array(tagsList.length);
  for (let i = 0; i < tagsList.length; i++) {
    const t = tagsList[i];
    t._ref = {
      name: t.name, slug: t.slug, url: t.url, count: t.posts.length,
      _jn: escHtmlJson(t.name), _jsl: escHtmlJson(t.slug), _ju: escHtmlJson(t.url),
    };
    tagCards[i] = t._ref;
  }
  const missingTagMap = new Map();

  let nextCid = 0;
  for (let i = 0; i < kept.length; i++) {
    const s = kept[i];
    const dateStr = s.data.date ?? '';
    const dlStr = dateStr === '' ? '' : longDate(dateStr);
    const sumStr = s.data.summary ?? '';
    const rm = Math.max(1, Math.ceil(s._words / 200));

    const tRefs = new Array(s.tagRefs.length);
    for (let k = 0; k < s.tagRefs.length; k++) {
      const tr = s.tagRefs[k];
      if (tr._ref !== undefined) { tRefs[k] = tr._ref; continue; }
      const ck = tr.slug + '\0' + tr.name;
      let mr = missingTagMap.get(ck);
      if (mr === undefined) {
        mr = { name: tr.name, slug: tr.slug, url: '', _jn: escHtmlJson(tr.name), _jsl: escHtmlJson(tr.slug), _ju: '' };
        missingTagMap.set(ck, mr);
      }
      tRefs[k] = mr;
    }

    const tocSrc = s._md.toc;
    const tocList = new Array(tocSrc.length);
    for (let k = 0; k < tocSrc.length; k++) {
      const h = tocSrc[k];
      tocList[k] = { level: h.level, id: h.id, html: h.html, _jid: h.id };
    }

    s.pageObj = {
      _cid: s.post ? nextCid++ : -1,
      title: s.data.title,
      url: s.url,
      date: dateStr,
      date_long: dlStr,
      summary: sumStr,
      excerpt: s._md.excerpt,
      reading_minutes: rm,
      slug: s.slug,
      content: s._md.html,
      is_post: s.post,
      tags: tRefs,
      toc: tocList,
      newer: null,
      older: null,
      _jt: escHtmlJson(s.data.title),
      _ju: escHtmlJson(s.url),
      _js: escHtmlJson(sumStr),
      _jslug: escHtmlJson(s.slug),
    };
  }

  for (let k = 0; k < posts.length; k++) {
    const p = posts[k];
    p.pageObj.newer = p.newer === null ? null : p.newer.pageObj;
    p.pageObj.older = p.older === null ? null : p.older.pageObj;
  }

  const cardCache = new Array(posts.length);
  const postCards = new Array(posts.length);
  for (let k = 0; k < posts.length; k++) postCards[k] = posts[k].pageObj;
  const recentCards = postCards.slice(0, input.site.recent);
  const tagPages = new Array(tagsList.length);
  for (let i = 0; i < tagsList.length; i++) {
    const t = tagsList[i];
    const tpPosts = new Array(t.posts.length);
    for (let k = 0; k < t.posts.length; k++) tpPosts[k] = t.posts[k].pageObj;
    tagPages[i] = { ...t._ref, posts: tpPosts };
  }

  const decodeJsonExcerpt = (ex) => (ex === '' || ex.indexOf('\\') === -1) ? ex : JSON.parse('"' + ex + '"');
  const plainRecent = new Array(recentCards.length);
  for (let i = 0; i < recentCards.length; i++) {
    const p = recentCards[i];
    plainRecent[i] = { ...p, excerpt: decodeJsonExcerpt(p.excerpt) };
  }
  const siteScope = { vars: { site: siteVar, tags: tagCards, recent: plainRecent }, parent: null };

  const compiledTpls = new Map();
  const getCompiled = (name, kind) => {
    const ck = name + ':' + kind;
    let c = compiledTpls.get(ck);
    if (c === undefined) {
      const raw = rawTpls.get(name);
      if (raw === undefined) { compiledTpls.set(ck, null); return null; }
      const inlined = inlineAstIncludes(raw, rawTpls, 0);
      const folded = foldInvariantNodes(inlined, siteScope);
      c = compileToConsFn(folded, kind);
      compiledTpls.set(ck, c);
    }
    return c;
  };

  let outJson = '{';
  let firstEntry = true;
  const writtenKeys = new Set();

  const pushKv = (kStr, valEscStr) => {
    writtenKeys.add(kStr);
    const kEsc = escJsonOnly(kStr);
    if (firstEntry) { outJson += '"' + kEsc + '":"' + valEscStr + '"'; firstEntry = false; }
    else outJson += ',"' + kEsc + '":"' + valEscStr + '"';
  };

  for (let i = 0; i < kept.length; i++) {
    const s = kept[i];
    const comp = getCompiled(s.layout, 'page');
    let baseSc = null;
    if (comp.needsDynScope) {
      const po = {
        ...s.pageObj,
        content: decodeJsonExcerpt(s.pageObj.content),
        excerpt: decodeJsonExcerpt(s.pageObj.excerpt),
        toc: s.pageObj.toc.map((h) => ({ ...h, html: decodeJsonExcerpt(h.html) })),
      };
      baseSc = { vars: { site: siteVar, tags: tagCards, recent: plainRecent, page: po }, parent: null };
    }
    pushKv(`${s.outDir}/index.html`, comp.fn(comp.chunks, cardCache, STRING_JIT_HELPERS, baseSc, s.pageObj, null));
  }

  const per = input.site.per_page;
  const pages = Math.max(1, Math.ceil(posts.length / per));
  const indexUrl = (k) => (k === 1 ? `${base}/` : `${base}/page/${k}/`);
  const indexComp = getCompiled('index', 'index');
  if (indexComp !== null) {
    for (let k = 1; k <= pages; k++) {
      const slicePosts = postCards.slice((k - 1) * per, k * per);
      const url = indexUrl(k);
      const nUrl = k === 1 ? '' : indexUrl(k - 1);
      const oUrl = k === pages ? '' : indexUrl(k + 1);
      const pager = {
        number: k, total: pages, url, newer_url: nUrl, older_url: oUrl,
        _ju: escHtmlJson(url), _jn: escHtmlJson(nUrl), _jo: escHtmlJson(oUrl),
      };
      const baseSc = indexComp.needsDynScope ? { vars: { site: siteVar, tags: tagCards, recent: plainRecent, posts: slicePosts.map((p) => ({ ...p, excerpt: decodeJsonExcerpt(p.excerpt) })), pager }, parent: null } : null;
      pushKv(k === 1 ? 'index.html' : `page/${k}/index.html`, indexComp.fn(indexComp.chunks, cardCache, STRING_JIT_HELPERS, baseSc, slicePosts, pager));
    }
  }

  const tagComp = getCompiled('tag', 'tag');
  if (tagComp !== null) {
    for (let i = 0; i < tagPages.length; i++) {
      const tp = tagPages[i];
      const baseSc = tagComp.needsDynScope ? { vars: { site: siteVar, tags: tagCards, recent: plainRecent, tag: { ...tp, posts: tp.posts.map((p) => ({ ...p, excerpt: decodeJsonExcerpt(p.excerpt) })) } }, parent: null } : null;
      pushKv(`tags/${tp.slug}/index.html`, tagComp.fn(tagComp.chunks, cardCache, STRING_JIT_HELPERS, baseSc, tp, null));
    }
  }

  const tagsComp = getCompiled('tags', 'tags');
  if (tagsComp !== null) {
    const baseSc = tagsComp.needsDynScope ? { vars: { site: siteVar, tags: tagCards, recent: plainRecent }, parent: null } : null;
    pushKv('tags/index.html', tagsComp.fn(tagsComp.chunks, cardCache, STRING_JIT_HELPERS, baseSc, null, null));
  }

  for (let i = 0; i < statics.length; i++) {
    const f = statics[i];
    if (writtenKeys.has(f.path)) {
      report.push(`shadowed ${f.path}: a built page has its path`);
      continue;
    }
    if (f.path === 'build-report.txt') continue;
    pushKv(f.path, escJsonOnly(f.content));
  }

  const rLines = [...report, ...broken].sort(byCodeUnits);
  rLines.push(`built ${kept.length - posts.length} pages, ${posts.length} posts, ${tagsList.length} tags and ${statics.length} static files`);
  pushKv('build-report.txt', escJsonOnly(`${rLines.join('\n')}\n`));

  outJson += '}';
  return outJson;
}

function writeFdAll(fd, buf, len) {
  let off = 0;
  while (off < len) off += writeSync(fd, buf, off, len - off);
}

function runFile(inPath, outPath) {
  const cases = JSON.parse(readFileSync(inPath, 'utf8'));
  const fd = openSync(outPath, 'w');
  let p = 0;
  OUT_SLAB[p++] = 91; // '['
  for (let i = 0; i < cases.length; i++) {
    if (i > 0) OUT_SLAB[p++] = 44; // ','
    const siteJson = buildSiteJsonStr(cases[i].input);
    cases[i] = null; // Release input memory immediately per case
    const need = p + siteJson.length * 3 + 8;
    if (need > OUT_SLAB.length) {
      const exactBytes = Buffer.byteLength(siteJson, 'utf8');
      if (p + exactBytes + 8 > OUT_SLAB.length) {
        if (p > 0) {
          writeFdAll(fd, OUT_SLAB, p);
          p = 0;
        }
        ensureSlab(exactBytes + 8);
      }
    }
    p += OUT_SLAB.utf8Write(siteJson, p);
    // Keep OUT_SLAB <= 4MB flushed to OS after each case so slab never needs 18-36MB!
    if (i < cases.length - 1 && p > 2 * 1024 * 1024) {
      writeFdAll(fd, OUT_SLAB, p);
      p = 0;
    }
  }
  OUT_SLAB[p++] = 93; // ']'
  writeFdAll(fd, OUT_SLAB, p);
  closeSync(fd);
}

function run(input) {
  return JSON.parse(buildSiteJsonStr(input));
}

module.exports = { runFile, run };
