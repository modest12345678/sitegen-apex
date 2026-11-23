// sitegen-apex v6: Zero-ESM CJS + Raw-UTF8 Byte Streaming + Zero-Deopt K_* Kernels + Flat Bytecode VM
'use strict';

const { openSync, closeSync, readFileSync, writeSync } = require('node:fs');

// ---------------------------------------------------------------------------
// Reusable Pre-Allocated Slabs (reset offsets per case; grow on demand)
// ---------------------------------------------------------------------------
let BODY_SLAB = Buffer.allocUnsafe(4 * 1024 * 1024);
let PARA_BUF = Buffer.allocUnsafe(128 * 1024);
let LINK_BUF = Buffer.allocUnsafe(16 * 1024);
let HBUF = Buffer.allocUnsafe(8 * 1024 * 1024);
let CARD_SLAB = Buffer.allocUnsafe(2 * 1024 * 1024);
let OUT_SLAB = Buffer.allocUnsafe(8 * 1024 * 1024);

function growCap(cur, need) {
  let cap = cur;
  while (cap < need) cap *= 2;
  return Buffer.allocUnsafe(cap);
}

function ensureBodySlab(need, curBp) {
  if (need <= BODY_SLAB.length) return BODY_SLAB;
  const next = growCap(BODY_SLAB.length, need);
  if (curBp > 0) BODY_SLAB.copy(next, 0, 0, curBp);
  BODY_SLAB = next;
  return BODY_SLAB;
}

function ensureParaBuf(need) {
  if (need > PARA_BUF.length) PARA_BUF = growCap(PARA_BUF.length, need);
  return PARA_BUF;
}

function ensureLinkBuf(need) {
  if (need > LINK_BUF.length) LINK_BUF = growCap(LINK_BUF.length, need);
  return LINK_BUF;
}

function ensureHBuf(need, curP) {
  if (need <= HBUF.length) return HBUF;
  const next = growCap(HBUF.length, need);
  if (curP > 0) HBUF.copy(next, 0, 0, curP);
  HBUF = next;
  return HBUF;
}

function ensureCardSlab(need, curCp) {
  if (need <= CARD_SLAB.length) return CARD_SLAB;
  const next = growCap(CARD_SLAB.length, need);
  if (curCp > 0) CARD_SLAB.copy(next, 0, 0, curCp);
  CARD_SLAB = next;
  return CARD_SLAB;
}

function ensureOutSlab(need, curOp) {
  if (need <= OUT_SLAB.length) return OUT_SLAB;
  const next = growCap(OUT_SLAB.length, need);
  if (curOp > 0) OUT_SLAB.copy(next, 0, 0, curOp);
  OUT_SLAB = next;
  return OUT_SLAB;
}

// ---------------------------------------------------------------------------
// 256-entry Byte Lookup Tables (branch-free ASCII + 128..255 passthrough)
// ---------------------------------------------------------------------------
const HJ_LEN = new Uint8Array(256);
const HJ_FLAT = new Uint8Array(256 * 8);
const J_LEN = new Uint8Array(256);
const J_FLAT = new Uint8Array(256 * 8);
const HEX_B = Buffer.from('0123456789abcdef', 'ascii');

function setTblStr(tblLen, tblFlat, code, str) {
  tblLen[code] = str.length;
  const off = code << 3;
  for (let i = 0; i < str.length; i++) tblFlat[off + i] = str.charCodeAt(i);
}

for (let i = 0; i < 32; i++) {
  let esc = '\\u00' + String.fromCharCode(HEX_B[i >> 4], HEX_B[i & 15]);
  if (i === 8) esc = '\\b';
  else if (i === 9) esc = '\\t';
  else if (i === 10) esc = '\\n';
  else if (i === 12) esc = '\\f';
  else if (i === 13) esc = '\\r';
  setTblStr(HJ_LEN, HJ_FLAT, i, esc);
  setTblStr(J_LEN, J_FLAT, i, esc);
}
setTblStr(HJ_LEN, HJ_FLAT, 34, '&quot;');
setTblStr(HJ_LEN, HJ_FLAT, 38, '&amp;');
setTblStr(HJ_LEN, HJ_FLAT, 39, '&#39;');
setTblStr(HJ_LEN, HJ_FLAT, 60, '&lt;');
setTblStr(HJ_LEN, HJ_FLAT, 62, '&gt;');
setTblStr(HJ_LEN, HJ_FLAT, 92, '\\\\');

setTblStr(J_LEN, J_FLAT, 34, '\\"');
setTblStr(J_LEN, J_FLAT, 92, '\\\\');

const MD_LUT = new Uint8Array(HJ_LEN);
MD_LUT[42] = 1; // '*'
MD_LUT[91] = 1; // '['
MD_LUT[92] = 1; // '\'
MD_LUT[96] = 1; // '`'

const UNESC_TBL = new Uint8Array(256);
UNESC_TBL[110] = 10; // \n
UNESC_TBL[34] = 34;  // \"
UNESC_TBL[92] = 92;  // \\
UNESC_TBL[116] = 9;  // \t
UNESC_TBL[98] = 8;   // \b
UNESC_TBL[102] = 12; // \f
UNESC_TBL[47] = 47;  // \/

const ESCAPABLE_CC = new Uint8Array(256);
for (const ch of '\\`*_[]()#+-!>.') ESCAPABLE_CC[ch.charCodeAt(0)] = 1;

const WS_TBL = new Uint8Array(256);
WS_TBL[9] = 1; WS_TBL[10] = 1; WS_TBL[11] = 1; WS_TBL[12] = 1; WS_TBL[13] = 1; WS_TBL[32] = 1;

const SLUG_TBL = new Uint8Array(256);
for (let c = 48; c <= 57; c++) SLUG_TBL[c] = c;
for (let c = 65; c <= 90; c++) SLUG_TBL[c] = c + 32;
for (let c = 97; c <= 122; c++) SLUG_TBL[c] = c;

const LANG_CC = new Uint8Array(256);
for (let c = 48; c <= 57; c++) LANG_CC[c] = 1;
for (let c = 65; c <= 90; c++) LANG_CC[c] = 1;
for (let c = 97; c <= 122; c++) LANG_CC[c] = 1;
LANG_CC[95] = 1; LANG_CC[43] = 1; LANG_CC[45] = 1;

const SCHEME_F = new Uint8Array(256);
const SCHEME_R = new Uint8Array(256);
for (let c = 65; c <= 90; c++) { SCHEME_F[c] = 1; SCHEME_R[c] = 1; }
for (let c = 97; c <= 122; c++) { SCHEME_F[c] = 1; SCHEME_R[c] = 1; }
for (let c = 48; c <= 57; c++) SCHEME_R[c] = 1;
SCHEME_R[43] = 1; SCHEME_R[45] = 1; SCHEME_R[46] = 1;

const MAY_END_PARA = new Uint8Array(256);
MAY_END_PARA[9] = 1; MAY_END_PARA[32] = 1; MAY_END_PARA[35] = 1;
MAY_END_PARA[42] = 1; MAY_END_PARA[45] = 1; MAY_END_PARA[96] = 1;

const PRE_FENCE_O = Buffer.from('<pre><code');
const PRE_FENCE_LANG = Buffer.from(' class=\\"language-');
const PRE_FENCE_C = Buffer.from('</code></pre>\\n');
const PRE_HR = Buffer.from('<hr>\\n');
const PRE_BQ_EMPTY = Buffer.from('<blockquote>\\n</blockquote>\\n');
const PRE_BQ_O = Buffer.from('<blockquote>\\n<p>');
const PRE_BQ_C = Buffer.from('</p>\\n</blockquote>\\n');
const PRE_UL_O = Buffer.from('<ul>\\n');
const PRE_UL_C = Buffer.from('</ul>\\n');
const PRE_OL_O1 = Buffer.from('<ol>\\n');
const PRE_OL_C = Buffer.from('</ol>\\n');
const PRE_LI_O = Buffer.from('<li>');
const PRE_LI_C = Buffer.from('</li>\\n');

// ---------------------------------------------------------------------------
// Text / String / Unicode Helpers
// ---------------------------------------------------------------------------
const SLUG_MAX = 64;
const byCodeUnits = (a, b) => (a < b ? -1 : a > b ? 1 : 0);
const MONTHS = ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December'];
const RESERVED = ['posts', 'tags', 'page'];
const SLUG_SCRATCH = Buffer.allocUnsafe(64);

function isUnicodeWsCp(cp) {
  return cp === 0x00A0 || cp === 0x1680 || (cp >= 0x2000 && cp <= 0x200A) || cp === 0x2028 || cp === 0x2029 || cp === 0x202F || cp === 0x205F || cp === 0x3000 || cp === 0xFEFF;
}

// Returns +nextIdx if multi-byte UTF-8 at i is Unicode WS, or -nextIdx if non-WS (Smi only, zero alloc).
function nonAsciiWsStep(buf, i, end) {
  const b0 = buf[i];
  if (b0 < 0xE0) {
    if (b0 >= 0xC2 && i + 1 < end) {
      const b1 = buf[i + 1];
      if ((b1 & 0xC0) === 0x80) {
        const cp = ((b0 & 0x1F) << 6) | (b1 & 0x3F);
        return cp === 0x00A0 ? (i + 2) : -(i + 2);
      }
    }
    return -(i + 1);
  }
  if (b0 < 0xF0) {
    if (i + 2 < end) {
      const b1 = buf[i + 1], b2 = buf[i + 2];
      if ((b1 & 0xC0) === 0x80 && (b2 & 0xC0) === 0x80) {
        const cp = ((b0 & 0x0F) << 12) | ((b1 & 0x3F) << 6) | (b2 & 0x3F);
        return isUnicodeWsCp(cp) ? (i + 3) : -(i + 3);
      }
    }
    return -(i + 1);
  }
  if (b0 <= 0xF4 && i + 3 < end) {
    if ((buf[i + 1] & 0xC0) === 0x80 && (buf[i + 2] & 0xC0) === 0x80 && (buf[i + 3] & 0xC0) === 0x80) {
      return -(i + 4);
    }
  }
  return -(i + 1);
}

function slugifyStr(text) {
  const n = text.length;
  for (let i = 0; i < n; i++) {
    if (text.charCodeAt(i) >= 128) return slugifyUnicode(text);
  }
  let outLen = 0;
  let gap = false;
  for (let i = 0; i < n; i++) {
    const mapped = SLUG_TBL[text.charCodeAt(i)];
    if (mapped === 0) {
      gap = outLen > 0;
      continue;
    }
    if (gap) {
      if (outLen === SLUG_MAX) break;
      SLUG_SCRATCH[outLen++] = 45;
      gap = false;
      if (outLen === SLUG_MAX) break;
    }
    SLUG_SCRATCH[outLen++] = mapped;
    if (outLen === SLUG_MAX) break;
  }
  while (outLen > 0 && SLUG_SCRATCH[outLen - 1] === 45) outLen--;
  return outLen === 0 ? 'untitled' : SLUG_SCRATCH.toString('latin1', 0, outLen);
}

function slugifyBuf(buf, s, e) {
  for (let i = s; i < e; i++) {
    if (buf[i] >= 128) return slugifyUnicode(buf.toString('utf8', s, e));
  }
  let outLen = 0;
  let gap = false;
  for (let i = s; i < e; i++) {
    const mapped = SLUG_TBL[buf[i]];
    if (mapped === 0) {
      gap = outLen > 0;
      continue;
    }
    if (gap) {
      if (outLen === SLUG_MAX) break;
      SLUG_SCRATCH[outLen++] = 45;
      gap = false;
      if (outLen === SLUG_MAX) break;
    }
    SLUG_SCRATCH[outLen++] = mapped;
    if (outLen === SLUG_MAX) break;
  }
  while (outLen > 0 && SLUG_SCRATCH[outLen - 1] === 45) outLen--;
  return outLen === 0 ? 'untitled' : SLUG_SCRATCH.toString('latin1', 0, outLen);
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

// Plain JS string escaping helpers (for small metadata, templates, dynamic fallback)
const HJ_RE_G = /[&<>"'\\\x00-\x1f]/g;
const HJ_TEST_RE = /[&<>"'\\\x00-\x1f]/;
const J_RE_G = /["\\\x00-\x1f]/g;
const J_TEST_RE = /["\\\x00-\x1f]/;
const HJ_PLAIN_RE = /[&<>"']/g;
const HJ_MAP = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;', '\\': '\\\\', '\n': '\\n', '\r': '\\r', '\t': '\\t', '\b': '\\b', '\f': '\\f' };
for (let i = 0; i < 32; i++) {
  const ch = String.fromCharCode(i);
  if (!Object.hasOwn(HJ_MAP, ch)) HJ_MAP[ch] = '\\u00' + i.toString(16).padStart(2, '0');
}
const J_MAP = { ...HJ_MAP, '"': '\\"' };
delete J_MAP['&']; delete J_MAP['<']; delete J_MAP['>']; delete J_MAP["'"];
const hjMapFn = (c) => HJ_MAP[c];
const jMapFn = (c) => J_MAP[c];

function escHtmlJsonStr(str) {
  if (str === '' || !HJ_TEST_RE.test(str)) return str;
  return str.replace(HJ_RE_G, hjMapFn);
}
function escJsonStr(str) {
  if (str === '' || !J_TEST_RE.test(str)) return str;
  return str.replace(J_RE_G, jMapFn);
}
function escHtmlPlain(str) {
  return str.replace(HJ_PLAIN_RE, hjMapFn);
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

// ---------------------------------------------------------------------------
// Zero-Deopt Selective TurboFan K_* Kernels
// ---------------------------------------------------------------------------

// K1: Unescape a JSON string span [s..e) into dst[0..], normalizing \r\n and \r -> \n.
// Returns unescaped byte length, or -1 if a \uXXXX or unrecognized escape is hit.
function K_unescMd(src, s, e, dst, dp, tbl) {
  let i = s | 0;
  let p = dp | 0;
  const end = e | 0;
  while (i < end) {
    const b = src[i];
    if (b === 92) {
      const c = src[i + 1];
      const m = tbl[c];
      if (m !== 0) {
        dst[p++] = m;
        i += 2;
      } else if (c === 114) {
        dst[p++] = 10;
        i += 2;
        if (i + 1 < end && src[i] === 92 && src[i + 1] === 110) i += 2;
      } else {
        return -1;
      }
    } else {
      dst[p++] = b;
      i++;
    }
  }
  return p - dp;
}

// SIMD-assisted JSON string end finder on latin1 view.
function findStrEnd(lat, s) {
  let q = lat.indexOf('"', s);
  while (q !== -1) {
    let bs = q - 1;
    while (bs >= s && lat.charCodeAt(bs) === 92) bs--;
    if (((q - 1 - bs) & 1) === 0) return q;
    q = lat.indexOf('"', q + 1);
  }
  return -1;
}

// K2: Count words in UTF-8 Buffer [s..e) matching JS String(/\S+/g) exact whitespace rules.
function K_wordsU8(buf, s, e, wsTbl) {
  let words = 0;
  let inW = 0;
  let i = s | 0;
  const end = e | 0;
  while (i < end) {
    const c = buf[i];
    if (c < 128) {
      if (wsTbl[c] === 0) {
        if (inW === 0) { words++; inW = 1; }
      } else {
        inW = 0;
      }
      i++;
    } else {
      const r = nonAsciiWsStep(buf, i, end);
      if (r > 0) {
        inW = 0;
        i = r;
      } else {
        if (inW === 0) { words++; inW = 1; }
        i = -r;
      }
    }
  }
  return words;
}

// K3: 25-line zero-deopt fast scanner + HTML/JSON escaper (stops on lut[b]===1 for MD syntax).
const SCAN_P = new Int32Array(1);
function K_scanEsc(src, s, e, out, p, lut, flat) {
  let i = s | 0;
  const end = e | 0;
  let op = p | 0;
  while (i < end) {
    const st = i;
    while (i < end && lut[src[i]] === 0) i++;
    const n = i - st;
    if (n > 0) {
      if (n <= 40) {
        for (let k = st; k < i; k++) out[op++] = src[k];
      } else {
        src.copy(out, op, st, i);
        op += n;
      }
    }
    if (i >= end) break;
    const ch = src[i];
    const code = lut[ch];
    if (code === 1) break;
    const off = ch << 3;
    for (let k = 0; k < code; k++) out[op++] = flat[off + k];
    i++;
  }
  SCAN_P[0] = op;
  return i;
}

// Byte helpers for mdInline & renderMarkdownIntoHBuf
function findUnescapedCharBuf(src, target, from, end) {
  const esc = ESCAPABLE_CC;
  for (let j = from; j < end; j++) {
    const c = src[j];
    if (c === 92 && j + 1 < end && esc[src[j + 1]] === 1) { j++; continue; }
    if (c === target) return j;
  }
  return -1;
}

function findUnescapedDStarBuf(src, from, end) {
  const esc = ESCAPABLE_CC;
  const lim = end - 1;
  for (let j = from; j < lim; j++) {
    const c = src[j];
    if (c === 92 && j + 1 < end && esc[src[j + 1]] === 1) { j++; continue; }
    if (c === 42 && src[j + 1] === 42) return j;
  }
  return -1;
}

function findSingleStarBuf(src, from, end) {
  const esc = ESCAPABLE_CC;
  for (let j = from; j < end; j++) {
    const c = src[j];
    if (c === 92 && j + 1 < end && esc[src[j + 1]] === 1) { j++; continue; }
    if (c !== 42) continue;
    if (j + 1 < end && src[j + 1] === 42) { j++; continue; }
    return j;
  }
  return -1;
}

function hasBufWhitespace(src, a, b) {
  const ws = WS_TBL;
  let i = a;
  while (i < b) {
    const c = src[i];
    if (c < 128) {
      if (ws[c] === 1) return true;
      i++;
    } else {
      const r = nonAsciiWsStep(src, i, b);
      if (r > 0) return true;
      i = -r;
    }
  }
  return false;
}

function isSchemeBuf(src, a, b) {
  if (a >= b || SCHEME_F[src[a]] === 0) return false;
  for (let i = a + 1; i < b; i++) {
    const c = src[i];
    if (c === 58) return true;
    if (SCHEME_R[c] === 0) return false;
  }
  return false;
}

function writeResolvedHref(src, hs, he, remEnd, p, ctx) {
  const c0 = src[hs];
  if (c0 === 47 || c0 === 35 || isSchemeBuf(src, hs, he)) {
    const need = p + (he - hs) * 6 + remEnd * 6 + 65536;
    if (need > HBUF.length) ensureHBuf(need, p);
    K_scanEsc(src, hs, he, HBUF, p, HJ_LEN, HJ_FLAT);
    return SCAN_P[0];
  }
  const target = src.toString('utf8', hs, he);
  let resolved;
  const hash = target.indexOf('#');
  const rel = hash === -1 ? target : target.slice(0, hash);
  const frag = hash === -1 ? '' : target.slice(hash);
  const out = rel === '' ? null : resolveRelPathParts(ctx.dirParts, rel);
  if (out !== null) {
    const hit = ctx.bySource.get(out);
    if (hit !== undefined) resolved = hit.url + frag;
    else if (ctx.staticSet.has(out)) resolved = ctx.base + '/' + out + frag;
    else {
      ctx.broken.add('broken-link ' + ctx.srcPath + ' -> ' + target);
      resolved = target;
    }
  } else {
    ctx.broken.add('broken-link ' + ctx.srcPath + ' -> ' + target);
    resolved = target;
  }
  const lb = ensureLinkBuf(resolved.length * 3 + 16);
  const nb = lb.utf8Write(resolved, 0);
  const need = p + nb * 6 + remEnd * 6 + 65536;
  if (need > HBUF.length) ensureHBuf(need, p);
  K_scanEsc(lb, 0, nb, HBUF, p, HJ_LEN, HJ_FLAT);
  return SCAN_P[0];
}

// Single-pass Byte-Native Inline Markdown using K_scanEsc.
function mdInline(src, s, e, p, ctx) {
  let i = s | 0;
  const end = e | 0;
  while (i < end) {
    i = K_scanEsc(src, i, end, HBUF, p, MD_LUT, HJ_FLAT);
    p = SCAN_P[0];
    if (i >= end) break;
    let dst = HBUF;
    const ch = src[i];
    if (ch === 92) {
      if (i + 1 < end) {
        const nc = src[i + 1];
        if (ESCAPABLE_CC[nc] === 1) {
          if (nc === 62) {
            dst[p++] = 38; dst[p++] = 103; dst[p++] = 116; dst[p++] = 59; // &gt;
          } else if (nc === 92) {
            dst[p++] = 92; dst[p++] = 92; // \\
          } else {
            dst[p++] = nc;
          }
          i += 2;
          continue;
        }
      }
      dst[p++] = 92; dst[p++] = 92; // \\
      i++;
      continue;
    }
    if (ch === 96) {
      let j = i + 1;
      while (j < end && src[j] !== 96) j++;
      if (j < end && j > i + 1) {
        dst[p++] = 60; dst[p++] = 99; dst[p++] = 111; dst[p++] = 100; dst[p++] = 101; dst[p++] = 62; // <code>
        K_scanEsc(src, i + 1, j, dst, p, HJ_LEN, HJ_FLAT);
        p = SCAN_P[0];
        dst[p++] = 60; dst[p++] = 47; dst[p++] = 99; dst[p++] = 111; dst[p++] = 100; dst[p++] = 101; dst[p++] = 62; // </code>
        i = j + 1;
      } else {
        dst[p++] = 96;
        i++;
      }
      continue;
    }
    if (ch === 42) {
      if (i + 1 < end && src[i + 1] === 42) {
        const j = findUnescapedDStarBuf(src, i + 2, end);
        if (j > i + 2) {
          dst[p++] = 60; dst[p++] = 115; dst[p++] = 116; dst[p++] = 114; dst[p++] = 111; dst[p++] = 110; dst[p++] = 103; dst[p++] = 62; // <strong>
          p = mdInline(src, i + 2, j, p, ctx);
          dst = HBUF;
          dst[p++] = 60; dst[p++] = 47; dst[p++] = 115; dst[p++] = 116; dst[p++] = 114; dst[p++] = 111; dst[p++] = 110; dst[p++] = 103; dst[p++] = 62; // </strong>
          i = j + 2;
        } else {
          dst[p++] = 42; dst[p++] = 42;
          i += 2;
        }
      } else {
        const j = findSingleStarBuf(src, i + 1, end);
        if (j > i + 1) {
          dst[p++] = 60; dst[p++] = 101; dst[p++] = 109; dst[p++] = 62; // <em>
          p = mdInline(src, i + 1, j, p, ctx);
          dst = HBUF;
          dst[p++] = 60; dst[p++] = 47; dst[p++] = 101; dst[p++] = 109; dst[p++] = 62; // </em>
          i = j + 1;
        } else {
          dst[p++] = 42;
          i++;
        }
      }
      continue;
    }
    // ch === 91 '['
    const k = findUnescapedCharBuf(src, 93, i + 1, end);
    if (k !== -1 && k + 1 < end && src[k + 1] === 40) {
      let m = k + 2;
      while (m < end && src[m] !== 41) m++;
      if (m < end && m > k + 2 && !hasBufWhitespace(src, k + 2, m)) {
        dst[p++] = 60; dst[p++] = 97; dst[p++] = 32; dst[p++] = 104; dst[p++] = 114; dst[p++] = 101; dst[p++] = 102; dst[p++] = 61; dst[p++] = 92; dst[p++] = 34; // <a href=\"
        p = writeResolvedHref(src, k + 2, m, end - m, p, ctx);
        dst = HBUF;
        dst[p++] = 92; dst[p++] = 34; dst[p++] = 62; // \">
        p = mdInline(src, i + 1, k, p, ctx);
        dst = HBUF;
        dst[p++] = 60; dst[p++] = 47; dst[p++] = 97; dst[p++] = 62; // </a>
        i = m + 1;
        continue;
      }
    }
    dst[p++] = 91;
    i++;
  }
  return p;
}

function writeOutEscJsonStr(str, op) {
  const escaped = escJsonStr(str);
  const maxB = escaped.length * 3 + 16;
  const dst = op + maxB > OUT_SLAB.length ? ensureOutSlab(op + maxB, op) : OUT_SLAB;
  return op + dst.utf8Write(escaped, op);
}

function writeOutUint(n, op) {
  const dst = op + 16 > OUT_SLAB.length ? ensureOutSlab(op + 16, op) : OUT_SLAB;
  if (n === 0) { dst[op++] = 48; return op; }
  let v = n | 0;
  let len = 0;
  while (v > 0) {
    len++;
    v = (v / 10) | 0;
  }
  let end = op + len;
  v = n | 0;
  for (let k = end - 1; k >= op; k--) {
    const q = (v / 10) | 0;
    dst[k] = 48 + (v - q * 10);
    v = q;
  }
  return end;
}

// ---------------------------------------------------------------------------
// Pre-allocated Site / VM State Tables (reused across cases)
// ---------------------------------------------------------------------------
const PF_STRIDE = 8; // 0:title 1:url 2:date 3:date_long 4:summary 5:slug 6:excerpt 7:content
const TF_STRIDE = 3; // 0:name 1:slug 2:url

const VM_S = {
  pOff: new Int32Array(1024 * PF_STRIDE),
  pLen: new Int32Array(1024 * PF_STRIDE),
  pReadMin: new Int32Array(1024),
  pIsPost: new Uint8Array(1024),
  pCid: new Int32Array(1024),
  pNewer: new Int32Array(1024),
  pOlder: new Int32Array(1024),
  pTagStart: new Int32Array(1024),
  pTagCount: new Int32Array(1024),
  pTocStart: new Int32Array(1024),
  pTocCount: new Int32Array(1024),
  allPageTags: new Int32Array(4096),
  postPids: new Int32Array(1024),

  tocLevel: new Int32Array(4096),
  tocIdOff: new Int32Array(4096),
  tocIdLen: new Int32Array(4096),
  tocHtmlOff: new Int32Array(4096),
  tocHtmlLen: new Int32Array(4096),

  tOff: new Int32Array(256 * TF_STRIDE),
  tLen: new Int32Array(256 * TF_STRIDE),
  tCount: new Int32Array(256),
  tPostStart: new Int32Array(256),
  tPostCount: new Int32Array(256),
  allTagPosts: new Int32Array(4096),

  cardOff: new Int32Array(1024),
  cardLen: new Int32Array(1024),

  pgOff: new Int32Array(3),
  pgLen: new Int32Array(3),
  pgNumber: 1,
  pgTotal: 1,
  curPostStart: 0,
  curPostLen: 0,

  regVal: new Int32Array(10),
  loopIdx: new Int32Array(10),
  loopLen: new Int32Array(10),
  curArrPos: new Int32Array(10),
  curArrEnd: new Int32Array(10),
  curArrKind: new Int32Array(10),
  curItemReg: new Int32Array(10),
  cardStartOp: -1,
  pendingCid: -1,
  cp: 0,
};

function ensurePageCap(n) {
  if (n <= VM_S.pReadMin.length) return;
  let cap = VM_S.pReadMin.length;
  while (cap < n) cap *= 2;
  VM_S.pOff = new Int32Array(cap * PF_STRIDE);
  VM_S.pLen = new Int32Array(cap * PF_STRIDE);
  VM_S.pReadMin = new Int32Array(cap);
  VM_S.pIsPost = new Uint8Array(cap);
  VM_S.pCid = new Int32Array(cap);
  VM_S.pNewer = new Int32Array(cap);
  VM_S.pOlder = new Int32Array(cap);
  VM_S.pTagStart = new Int32Array(cap);
  VM_S.pTagCount = new Int32Array(cap);
  VM_S.pTocStart = new Int32Array(cap);
  VM_S.pTocCount = new Int32Array(cap);
  VM_S.postPids = new Int32Array(cap);
  VM_S.cardOff = new Int32Array(cap);
  VM_S.cardLen = new Int32Array(cap);
}

function ensureTagCap(n) {
  if (n <= VM_S.tCount.length) return;
  let cap = VM_S.tCount.length;
  while (cap < n) cap *= 2;
  VM_S.tOff = new Int32Array(cap * TF_STRIDE);
  VM_S.tLen = new Int32Array(cap * TF_STRIDE);
  VM_S.tCount = new Int32Array(cap);
  VM_S.tPostStart = new Int32Array(cap);
  VM_S.tPostCount = new Int32Array(cap);
}

function ensureTocCap(n) {
  if (n <= VM_S.tocLevel.length) return;
  let cap = VM_S.tocLevel.length;
  while (cap < n) cap *= 2;
  const old = VM_S;
  const nl = new Int32Array(cap); nl.set(old.tocLevel); old.tocLevel = nl;
  const nio = new Int32Array(cap); nio.set(old.tocIdOff); old.tocIdOff = nio;
  const nil = new Int32Array(cap); nil.set(old.tocIdLen); old.tocIdLen = nil;
  const nho = new Int32Array(cap); nho.set(old.tocHtmlOff); old.tocHtmlOff = nho;
  const nhl = new Int32Array(cap); nhl.set(old.tocHtmlLen); old.tocHtmlLen = nhl;
}

function ensureAllPageTagsCap(n) {
  if (n <= VM_S.allPageTags.length) return;
  let cap = VM_S.allPageTags.length;
  while (cap < n) cap *= 2;
  const next = new Int32Array(cap);
  next.set(VM_S.allPageTags);
  VM_S.allPageTags = next;
}

function ensureAllTagPostsCap(n) {
  if (n <= VM_S.allTagPosts.length) return;
  let cap = VM_S.allTagPosts.length;
  while (cap < n) cap *= 2;
  const next = new Int32Array(cap);
  next.set(VM_S.allTagPosts);
  VM_S.allTagPosts = next;
}

// ---------------------------------------------------------------------------
// Flat Bytecode Template VM (4 Int32 words per instruction)
// ---------------------------------------------------------------------------
const OP_LIT = 1;
const OP_STR = 2;
const OP_INT = 3;
const OP_BOOL = 4;
const OP_JMP = 5;
const OP_JCOND = 6;
const OP_FOR_INIT = 7;
const OP_FOR_NEXT = 8;
const OP_FOR_CARDS_INIT = 9;
const OP_FOR_CARDS_CHECK = 10;
const OP_FOR_CARDS_NEXT = 11;

function vmEvalCond(S, condKind, a2) {
  const reg = a2 >>> 16;
  const slot = (a2 >>> 8) & 255;
  const val = S.regVal[reg];
  if (condKind === 0) return S.pLen[val * PF_STRIDE + slot] > 0 ? 1 : 0;
  if (condKind === 1) {
    const nb = slot >= 16 ? S.pOlder[val] : S.pNewer[val];
    if (nb === -1) return 0;
    const f = slot & 15;
    if (f === 15) return 1;
    return S.pLen[nb * PF_STRIDE + f] > 0 ? 1 : 0;
  }
  if (condKind === 2) {
    if (slot === 0) return S.pIsPost[val] !== 0 ? 1 : 0;
    if (slot === 1) return S.pReadMin[val] !== 0 ? 1 : 0;
    if (slot === 2) return S.pTagCount[val] > 0 ? 1 : 0;
    return S.pTocCount[val] > 0 ? 1 : 0;
  }
  if (condKind === 3) {
    if (slot < 3) return S.tLen[val * TF_STRIDE + slot] > 0 ? 1 : 0;
    if (slot === 3) return S.tCount[val] > 0 ? 1 : 0;
    return S.tPostCount[val] > 0 ? 1 : 0;
  }
  if (condKind === 4) {
    if (slot === 0) return S.tocLevel[val] !== 0 ? 1 : 0;
    if (slot === 1) return S.tocIdLen[val] > 0 ? 1 : 0;
    return S.tocHtmlLen[val] > 0 ? 1 : 0;
  }
  if (condKind === 5) {
    if (slot < 3) return S.pgLen[slot] > 0 ? 1 : 0;
    return (slot === 3 ? S.pgNumber : S.pgTotal) !== 0 ? 1 : 0;
  }
  if (condKind === 6) {
    if (slot === 0) return S.loopIdx[reg] !== 0 ? 1 : 0;
    if (slot === 1) return S.loopLen[reg] !== 0 ? 1 : 0;
    if (slot === 2) return S.loopIdx[reg] === 1 ? 1 : 0;
    return S.loopIdx[reg] === S.loopLen[reg] ? 1 : 0;
  }
  return S.curPostLen > 0 ? 1 : 0;
}

function vmElemAt(S, arrKind, pos) {
  if (arrKind === 0) return S.postPids[pos];
  if (arrKind === 1) return S.allTagPosts[pos];
  if (arrKind === 2) return S.allPageTags[pos];
  return pos;
}

function execVm(ops, nWords, op, S) {
  let ip = 0;
  let dst = OUT_SLAB;
  let dstCap = dst.length;
  const h = HBUF;
  while (ip < nWords) {
    const code = ops[ip];
    const a1 = ops[ip + 1];
    const a2 = ops[ip + 2];
    const a3 = ops[ip + 3];
    ip += 4;
    if (code === OP_LIT) {
      if (a2 > 0) {
        if (op + a2 + 64 > dstCap) { dst = ensureOutSlab(op + a2 + 64, op); dstCap = dst.length; }
        if (a2 <= 40) {
          const end = a1 + a2;
          for (let k = a1; k < end; k++) dst[op++] = h[k];
        } else {
          h.copy(dst, op, a1, a1 + a2);
          op += a2;
        }
      }
    } else if (code === OP_STR) {
      let sOff = 0, sLen = 0;
      if (a1 === 0) {
        const idx = S.regVal[a2] * PF_STRIDE + a3;
        sOff = S.pOff[idx]; sLen = S.pLen[idx];
      } else if (a1 === 1 || a1 === 2) {
        const nb = a1 === 1 ? S.pNewer[S.regVal[a2]] : S.pOlder[S.regVal[a2]];
        if (nb !== -1) {
          const idx = nb * PF_STRIDE + a3;
          sOff = S.pOff[idx]; sLen = S.pLen[idx];
        }
      } else if (a1 === 3) {
        const idx = S.regVal[a2] * TF_STRIDE + a3;
        sOff = S.tOff[idx]; sLen = S.tLen[idx];
      } else if (a1 === 4) {
        const tocId = S.regVal[a2];
        if (a3 === 0) { sOff = S.tocIdOff[tocId]; sLen = S.tocIdLen[tocId]; }
        else { sOff = S.tocHtmlOff[tocId]; sLen = S.tocHtmlLen[tocId]; }
      } else {
        sOff = S.pgOff[a3]; sLen = S.pgLen[a3];
      }
      if (sLen > 0) {
        if (op + sLen + 64 > dstCap) { dst = ensureOutSlab(op + sLen + 64, op); dstCap = dst.length; }
        if (sLen <= 40) {
          const end = sOff + sLen;
          for (let k = sOff; k < end; k++) dst[op++] = h[k];
        } else {
          h.copy(dst, op, sOff, sOff + sLen);
          op += sLen;
        }
      }
    } else if (code === OP_INT) {
      let val = -1;
      if (a1 === 0) val = S.pReadMin[S.regVal[a2]];
      else if (a1 === 1) { const tc = S.tCount[S.regVal[a2]]; if (tc > 0) val = tc; }
      else if (a1 === 2) val = S.tocLevel[S.regVal[a2]];
      else if (a1 === 3) val = a3 === 0 ? S.pgNumber : S.pgTotal;
      else if (a1 === 4) val = S.loopIdx[a2];
      else val = S.loopLen[a2];
      if (val >= 0) {
        if (op + 16 > dstCap) { dst = ensureOutSlab(op + 64, op); dstCap = dst.length; }
        if (val < 10) {
          dst[op++] = 48 + val;
        } else if (val < 100) {
          const q = (val / 10) | 0;
          dst[op++] = 48 + q;
          dst[op++] = 48 + (val - q * 10);
        } else {
          op = writeOutUint(val, op);
        }
      }
    } else if (code === OP_BOOL) {
      let bv;
      if (a1 === 0) bv = S.pIsPost[S.regVal[a2]] !== 0;
      else if (a1 === 1) bv = S.loopIdx[a2] === 1;
      else bv = S.loopIdx[a2] === S.loopLen[a2];
      if (op + 8 > dstCap) { dst = ensureOutSlab(op + 64, op); dstCap = dst.length; }
      if (bv) { dst[op++] = 116; dst[op++] = 114; dst[op++] = 117; dst[op++] = 101; }
      else { dst[op++] = 102; dst[op++] = 97; dst[op++] = 108; dst[op++] = 115; dst[op++] = 101; }
    } else if (code === OP_JMP) {
      ip = a1;
    } else if (code === OP_JCOND) {
      const inv = a2 & 1;
      const tru = vmEvalCond(S, a1, a2);
      if ((tru ^ inv) === 0) ip = a3;
    } else if (code === OP_FOR_INIT) {
      const d = a1 >>> 8;
      const arrKind = a1 & 15;
      const itemReg = a2 & 15;
      const collReg = a2 >>> 8;
      let st, en;
      if (arrKind === 0) { st = S.curPostStart; en = st + S.curPostLen; }
      else if (arrKind === 1) { const t = S.regVal[collReg]; st = S.tPostStart[t]; en = st + S.tPostCount[t]; }
      else if (arrKind === 2) { const p = S.regVal[collReg]; st = S.pTagStart[p]; en = st + S.pTagCount[p]; }
      else { const p = S.regVal[collReg]; st = S.pTocStart[p]; en = st + S.pTocCount[p]; }
      const cnt = en - st;
      if (cnt <= 0) {
        ip = a3;
      } else {
        S.curArrPos[d] = st;
        S.curArrEnd[d] = en;
        S.curArrKind[d] = arrKind;
        S.curItemReg[d] = itemReg;
        S.loopIdx[d] = 1;
        S.loopLen[d] = cnt;
        S.regVal[itemReg] = vmElemAt(S, arrKind, st);
      }
    } else if (code === OP_FOR_NEXT) {
      const d = a1;
      const pos = S.curArrPos[d] + 1;
      if (pos < S.curArrEnd[d]) {
        S.curArrPos[d] = pos;
        S.loopIdx[d] += 1;
        S.regVal[S.curItemReg[d]] = vmElemAt(S, S.curArrKind[d], pos);
        ip = a2;
      }
    } else if (code === OP_FOR_CARDS_INIT) {
      const d = a1 >>> 8;
      const arrKind = a1 & 15;
      const itemReg = a2 & 15;
      const collReg = a2 >>> 8;
      const st = arrKind === 0 ? S.curPostStart : S.tPostStart[S.regVal[collReg]];
      const cnt = arrKind === 0 ? S.curPostLen : S.tPostCount[S.regVal[collReg]];
      if (cnt <= 0) {
        ip = a3;
      } else {
        S.curArrPos[d] = st;
        S.curArrEnd[d] = st + cnt;
        S.curArrKind[d] = arrKind;
        S.curItemReg[d] = itemReg;
        S.loopLen[d] = cnt;
        S.loopIdx[d] = 1;
      }
    } else if (code === OP_FOR_CARDS_CHECK) {
      const d = a1;
      const ak = S.curArrKind[d];
      let pos = S.curArrPos[d];
      const en = S.curArrEnd[d];
      let fellThrough = false;
      while (pos < en) {
        const pid = ak === 0 ? S.postPids[pos] : S.allTagPosts[pos];
        const cid = S.pCid[pid];
        const cLen = S.cardLen[cid];
        if (cLen >= 0) {
          if (op + cLen + 64 > dstCap) { dst = ensureOutSlab(op + cLen + 64, op); dstCap = dst.length; }
          const off = S.cardOff[cid];
          if (cLen <= 40) {
            const cb = CARD_SLAB;
            const end = off + cLen;
            for (let k = off; k < end; k++) dst[op++] = cb[k];
          } else {
            CARD_SLAB.copy(dst, op, off, off + cLen);
            op += cLen;
          }
          pos++;
          S.loopIdx[d] += 1;
        } else {
          S.curArrPos[d] = pos;
          S.regVal[S.curItemReg[d]] = pid;
          S.cardStartOp = op;
          S.pendingCid = cid;
          fellThrough = true;
          break;
        }
      }
      if (!fellThrough) ip = a2;
    } else if (code === OP_FOR_CARDS_NEXT) {
      const d = a1;
      const cid = S.pendingCid;
      if (cid !== -1) {
        const cs = S.cardStartOp;
        const cLen = op - cs;
        const need = S.cp + cLen;
        const cb = need > CARD_SLAB.length ? ensureCardSlab(need, S.cp) : CARD_SLAB;
        dst.copy(cb, S.cp, cs, op);
        S.cardOff[cid] = S.cp;
        S.cardLen[cid] = cLen;
        S.cp = need;
        S.pendingCid = -1;
      }
      const pos = S.curArrPos[d] + 1;
      S.curArrPos[d] = pos;
      S.loopIdx[d] += 1;
      if (pos < S.curArrEnd[d]) ip = a2;
    }
  }
  return op;
}

// ---------------------------------------------------------------------------
// Byte-Native Frontmatter Parser
// ---------------------------------------------------------------------------
const DAYS_NORM = [0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
function isValidDateBuf(buf, s, e) {
  if (e - s !== 10 || buf[s + 4] !== 45 || buf[s + 7] !== 45) return false;
  for (let i = 0; i < 10; i++) {
    if (i === 4 || i === 7) continue;
    const c = buf[s + i];
    if (c < 48 || c > 57) return false;
  }
  const y = (buf[s] - 48) * 1000 + (buf[s + 1] - 48) * 100 + (buf[s + 2] - 48) * 10 + (buf[s + 3] - 48);
  const m = (buf[s + 5] - 48) * 10 + (buf[s + 6] - 48);
  const d = (buf[s + 8] - 48) * 10 + (buf[s + 9] - 48);
  if (y < 1970 || y > 2099 || m < 1 || m > 12 || d < 1) return false;
  let md = DAYS_NORM[m];
  if (m === 2 && ((y % 4 === 0 && y % 100 !== 0) || y % 400 === 0)) md = 29;
  return d <= md;
}

function parseQuotedFmBuf(buf, s, e) {
  if (e - s < 2 || buf[e - 1] !== 34) return { error: 'a quoted string is not closed' };
  const innerS = s + 1;
  const innerE = e - 1;
  let hasSpecial = false;
  for (let i = innerS; i < innerE; i++) {
    if (buf[i] === 92 || buf[i] === 34) { hasSpecial = true; break; }
  }
  if (!hasSpecial) return { value: buf.toString('utf8', innerS, innerE) };
  let p = 0;
  const out = LINK_BUF.length < (innerE - innerS) ? ensureLinkBuf(innerE - innerS) : LINK_BUF;
  for (let i = innerS; i < innerE; i++) {
    const c = buf[i];
    if (c === 92) {
      if (i + 1 >= innerE) return { error: 'a quoted string holds an escape other than \\" or \\\\' };
      const n = buf[i + 1];
      if (n !== 34 && n !== 92) return { error: 'a quoted string holds an escape other than \\" or \\\\' };
      out[p++] = n;
      i++;
    } else if (c === 34) {
      return { error: 'a quoted string holds a stray quote' };
    } else {
      out[p++] = c;
    }
  }
  return { value: out.toString('utf8', 0, p) };
}

function fmBufEq(buf, s, e, lit) {
  const n = lit.length;
  if (e - s !== n) return false;
  for (let i = 0; i < n; i++) if (buf[s + i] !== lit.charCodeAt(i)) return false;
  return true;
}

const KEY_NAMES = ['title', 'date', 'tags', 'draft', 'layout', 'slug', 'summary'];

function parseFrontMatterBuf(buf, basePos, endLimit) {
  const len = endLimit;
  let nl = basePos;
  while (nl < len && buf[nl] !== 10) nl++;
  if (nl - basePos !== 3 || buf[basePos] !== 45 || buf[basePos + 1] !== 45 || buf[basePos + 2] !== 45) {
    return { error: 'no front matter' };
  }
  const bodyFmStart = nl + 1;
  let pos = bodyFmStart;
  let closePos = -1;
  let bodyStart = len;
  while (pos < len) {
    nl = pos;
    while (nl < len && buf[nl] !== 10) nl++;
    if (nl - pos === 3 && buf[pos] === 45 && buf[pos + 1] === 45 && buf[pos + 2] === 45) {
      closePos = pos;
      bodyStart = nl < len ? nl + 1 : len;
      break;
    }
    pos = nl + 1;
  }
  if (closePos === -1) return { error: 'the front matter is not closed' };

  const data = { title: '', date: '', summary: '', layout: '', slug: '', draft: false, tags: null };
  let seenMask = 0;
  pos = bodyFmStart;
  let idx = 1;
  while (pos < closePos) {
    nl = pos;
    while (nl < closePos && buf[nl] !== 10) nl++;
    const lEnd = nl;
    let blank = true;
    for (let k = pos; k < lEnd; k++) {
      const c = buf[k];
      if (c !== 32 && c !== 9) { blank = false; break; }
    }
    if (!blank && buf[pos] !== 35) {
      let colon = -1;
      for (let k = pos; k < lEnd; k++) {
        if (buf[k] === 58) { colon = k; break; }
      }
      if (colon === -1 || colon === pos) return { error: `line ${idx + 1} is not "key: value"` };
      for (let k = pos; k < colon; k++) {
        const b = buf[k];
        if (!((b >= 97 && b <= 122) || b === 95)) return { error: `line ${idx + 1} is not "key: value"` };
      }
      if (colon + 1 < lEnd && buf[colon + 1] !== 32) return { error: `line ${idx + 1} is not "key: value"` };
      let vs = colon + 2;
      let ve = lEnd;
      while (ve > vs && (buf[ve - 1] === 32 || buf[ve - 1] === 9)) ve--;

      const kLen = colon - pos;
      const k0 = buf[pos];
      let kid = -1;
      if (kLen === 5 && k0 === 116 && fmBufEq(buf, pos, colon, 'title')) kid = 0;
      else if (kLen === 4 && k0 === 100 && fmBufEq(buf, pos, colon, 'date')) kid = 1;
      else if (kLen === 4 && k0 === 116 && fmBufEq(buf, pos, colon, 'tags')) kid = 2;
      else if (kLen === 5 && k0 === 100 && fmBufEq(buf, pos, colon, 'draft')) kid = 3;
      else if (kLen === 6 && k0 === 108 && fmBufEq(buf, pos, colon, 'layout')) kid = 4;
      else if (kLen === 4 && k0 === 115 && fmBufEq(buf, pos, colon, 'slug')) kid = 5;
      else if (kLen === 7 && k0 === 115 && fmBufEq(buf, pos, colon, 'summary')) kid = 6;
      else return { error: `unknown key "${buf.toString('utf8', pos, colon)}"` };

      const bit = 1 << kid;
      if ((seenMask & bit) !== 0) return { error: `key "${KEY_NAMES[kid]}" is given twice` };
      seenMask |= bit;
      if (vs >= ve) return { error: `key "${KEY_NAMES[kid]}" has no value` };

      if (kid === 0 || kid === 6) {
        const b0 = buf[vs];
        let val;
        if (b0 === 34) {
          const qr = parseQuotedFmBuf(buf, vs, ve);
          if ('error' in qr) return { error: `key "${KEY_NAMES[kid]}": ${qr.error}` };
          val = qr.value;
        } else if (b0 === 91) {
          return { error: `key "${KEY_NAMES[kid]}": a bare string opens on [` };
        } else {
          val = buf.toString('utf8', vs, ve);
        }
        if (kid === 0) data.title = val;
        else data.summary = val;
      } else if (kid === 1) {
        if (!isValidDateBuf(buf, vs, ve)) return { error: 'key "date": not a date from 1970-01-01 to 2099-12-31 (YYYY-MM-DD)' };
        data.date = buf.toString('latin1', vs, ve);
      } else if (kid === 3) {
        if (fmBufEq(buf, vs, ve, 'true')) data.draft = true;
        else if (fmBufEq(buf, vs, ve, 'false')) data.draft = false;
        else return { error: 'key "draft": true or false' };
      } else if (kid === 4) {
        for (let k = vs; k < ve; k++) {
          const c = buf[k];
          if (!((c >= 97 && c <= 122) || (c >= 48 && c <= 57) || c === 45)) return { error: 'key "layout": not a template name' };
        }
        data.layout = buf.toString('latin1', vs, ve);
      } else if (kid === 5) {
        if (ve - vs > SLUG_MAX || buf[vs] === 45 || buf[ve - 1] === 45) return { error: 'key "slug": not a slug' };
        for (let k = vs; k < ve; k++) {
          const c = buf[k];
          const ok = (c >= 97 && c <= 122) || (c >= 48 && c <= 57) || (c === 45 && buf[k - 1] !== 45);
          if (!ok) return { error: 'key "slug": not a slug' };
        }
        data.slug = buf.toString('latin1', vs, ve);
      } else {
        if (buf[vs] !== 91 || buf[ve - 1] !== 93) return { error: 'key "tags": not a list [a, b]' };
        const rawT = buf.toString('utf8', vs + 1, ve - 1);
        if (rawT.trim() === '') data.tags = [];
        else {
          const tags = rawT.split(',').map((t) => t.trim());
          for (let ti = 0; ti < tags.length; ti++) {
            const tg = tags[ti];
            if (tg === '' || tg.includes('"') || tg.includes('[') || tg.includes(']')) {
              return { error: 'key "tags": an empty tag, or one holding " [ or ]' };
            }
          }
          data.tags = tags;
        }
      }
    }
    idx++;
    pos = lEnd + 1;
  }
  if ((seenMask & 1) === 0) return { error: 'no title' };
  return { data, bodyStart: bodyStart >= len ? len : bodyStart, bodyEnd: len, seenMask };
}

// ---------------------------------------------------------------------------
// Byte-Native Block Markdown Renderer -> writes straight into HBUF
// ---------------------------------------------------------------------------
function bufIsBlank(buf, s, e) {
  for (let i = s; i < e; i++) {
    const c = buf[i];
    if (c !== 32 && c !== 9) return false;
  }
  return true;
}

function bufFenceOpen(buf, s, e) {
  if (e - s < 3 || buf[s] !== 96 || buf[s + 1] !== 96 || buf[s + 2] !== 96) return -1;
  let i = s + 3;
  while (i < e && LANG_CC[buf[i]] === 1) i++;
  const langEnd = i;
  while (i < e) {
    const c = buf[i];
    if (c !== 32 && c !== 9) return -1;
    i++;
  }
  return langEnd;
}

function bufFenceClose(buf, s, e) {
  if (e - s < 3 || buf[s] !== 96 || buf[s + 1] !== 96 || buf[s + 2] !== 96) return false;
  for (let i = s + 3; i < e; i++) {
    const c = buf[i];
    if (c !== 32 && c !== 9) return false;
  }
  return true;
}

function bufIsHr(buf, s, e) {
  if (e - s < 3) return false;
  const c = buf[s];
  if ((c !== 45 && c !== 42) || buf[s + 1] !== c || buf[s + 2] !== c) return false;
  for (let i = s + 3; i < e; i++) {
    const b = buf[i];
    if (b !== 32 && b !== 9) return false;
  }
  return true;
}

let _bHd = 0, _bHs = 0, _bHe = 0;
function bufHeading(buf, s, e) {
  if (s >= e || buf[s] !== 35) return false;
  let d = 1;
  let i = s + 1;
  while (i < e && buf[i] === 35 && d < 7) { d++; i++; }
  if (d > 6 || i >= e || (buf[i] !== 32 && buf[i] !== 9)) return false;
  i++;
  while (i < e && (buf[i] === 32 || buf[i] === 9)) i++;
  let end = e;
  while (end > i && (buf[end - 1] === 32 || buf[end - 1] === 9)) end--;
  if (end <= i) return false;
  _bHd = d; _bHs = i; _bHe = end;
  return true;
}

function bufEndsPara(buf, s, e) {
  if (s >= e) return true;
  const c0 = buf[s];
  if (MAY_END_PARA[c0] === 0) return false;
  if (c0 === 32 || c0 === 9) return bufIsBlank(buf, s, e);
  if (c0 === 96) return bufFenceOpen(buf, s, e) !== -1;
  if (c0 === 35) return bufHeading(buf, s, e);
  return bufIsHr(buf, s, e);
}

function bufMatchOrd(buf, s, e) {
  if (s >= e) return -1;
  let i = s, digits = 0;
  while (i < e) {
    const c = buf[i];
    if (c < 48 || c > 57) break;
    digits++;
    if (digits > 9) return -1;
    i++;
  }
  if (digits === 0 || i + 1 >= e || buf[i] !== 46 || buf[i + 1] !== 32) return -1;
  return i + 2;
}

function bufIsContinued(buf, s, e) {
  if (e - s < 3 || buf[s] !== 32 || buf[s + 1] !== 32) return false;
  let i = s + 2;
  while (i < e && buf[i] === 32) i++;
  if (i >= e) return false;
  const c = buf[i];
  if (c < 128) return WS_TBL[c] === 0;
  return nonAsciiWsStep(buf, i, e) < 0;
}

function appendTrimToPara(buf, s, e, pLen) {
  while (s < e && (buf[s] === 32 || buf[s] === 9)) s++;
  while (e > s && (buf[e - 1] === 32 || buf[e - 1] === 9)) e--;
  const n = e - s;
  if (n <= 0) return pLen;
  const pb = ensureParaBuf(pLen + n + 2);
  if (pLen > 0) pb[pLen++] = 10;
  if (n <= 40) {
    for (let k = s; k < e; k++) pb[pLen++] = buf[k];
  } else {
    buf.copy(pb, pLen, s, e);
    pLen += n;
  }
  return pLen;
}

function hCopyPre(pre, p) {
  const n = pre.length;
  const dst = HBUF;
  for (let k = 0; k < n; k++) dst[p++] = pre[k];
  return p;
}

const REUSABLE_HIDS = new Set();

function renderMarkdownIntoHBuf(buf, bodyS, bodyE, hpStart, linkCtx, tocOut) {
  REUSABLE_HIDS.clear();
  let p = hpStart;
  const needBase = p + (bodyE - bodyS) * 8 + 262144;
  if (needBase > HBUF.length) ensureHBuf(needBase, p);

  let pos = bodyS;
  let exOff = 0, exLen = -1;
  const len = bodyE;

  while (pos <= len) {
    if (pos === len && len > bodyS && buf[len - 1] === 10) break;
    let nl = pos;
    while (nl < len && buf[nl] !== 10) nl++;
    let lEnd = nl;
    const c0 = pos < lEnd ? buf[pos] : -1;

    if (c0 === -1) {
      if (pos >= len) break;
      pos = nl + 1;
      continue;
    }

    if (c0 === 32 || c0 === 9 || c0 === 96 || c0 === 35 || c0 === 45 || c0 === 42 || c0 === 62 || (c0 >= 48 && c0 <= 57)) {
      if ((c0 === 32 || c0 === 9) && bufIsBlank(buf, pos, lEnd)) {
        if (pos >= len) break;
        pos = nl + 1;
        continue;
      }
      if (c0 === 96) {
        const langEnd = bufFenceOpen(buf, pos, lEnd);
        if (langEnd !== -1) {
          p = hCopyPre(PRE_FENCE_O, p);
          if (langEnd > pos + 3) {
            p = hCopyPre(PRE_FENCE_LANG, p);
            K_scanEsc(buf, pos + 3, langEnd, HBUF, p, HJ_LEN, HJ_FLAT);
            p = SCAN_P[0];
            HBUF[p++] = 92; HBUF[p++] = 34; // \"
          }
          HBUF[p++] = 62; // >
          pos = nl + 1;
          while (pos <= len) {
            nl = pos;
            while (nl < len && buf[nl] !== 10) nl++;
            lEnd = nl;
            if (bufFenceClose(buf, pos, lEnd)) {
              pos = nl + 1;
              break;
            }
            if (lEnd > pos) {
              K_scanEsc(buf, pos, lEnd, HBUF, p, HJ_LEN, HJ_FLAT);
              p = SCAN_P[0];
            }
            HBUF[p++] = 92; HBUF[p++] = 110; // \n
            if (pos >= len) { pos = len + 1; break; }
            pos = nl + 1;
          }
          p = hCopyPre(PRE_FENCE_C, p);
          continue;
        }
      }
      if (c0 === 35 && bufHeading(buf, pos, lEnd)) {
        const d = _bHd;
        const id = uniqueSlug(slugifyBuf(buf, _bHs, _bHe), REUSABLE_HIDS);
        const dst = HBUF;
        dst[p++] = 60; dst[p++] = 104; dst[p++] = 48 + d;
        dst[p++] = 32; dst[p++] = 105; dst[p++] = 100; dst[p++] = 61; dst[p++] = 92; dst[p++] = 34;
        const idOff = p;
        for (let k = 0; k < id.length; k++) dst[p++] = id.charCodeAt(k);
        const idLen = p - idOff;
        dst[p++] = 92; dst[p++] = 34; dst[p++] = 62;
        const hInlStart = p;
        p = mdInline(buf, _bHs, _bHe, p, linkCtx);
        const hInlLen = p - hInlStart;
        const d2 = HBUF;
        d2[p++] = 60; d2[p++] = 47; d2[p++] = 104; d2[p++] = 48 + d; d2[p++] = 62; d2[p++] = 92; d2[p++] = 110;
        if (d === 2 || d === 3) {
          const tid = tocOut.count;
          ensureTocCap(tid + 1);
          VM_S.tocLevel[tid] = d;
          VM_S.tocIdOff[tid] = idOff;
          VM_S.tocIdLen[tid] = idLen;
          VM_S.tocHtmlOff[tid] = hInlStart;
          VM_S.tocHtmlLen[tid] = hInlLen;
          tocOut.count = tid + 1;
        }
        if (pos >= len) break;
        pos = nl + 1;
        continue;
      }
      if ((c0 === 45 || c0 === 42) && bufIsHr(buf, pos, lEnd)) {
        p = hCopyPre(PRE_HR, p);
        if (pos >= len) break;
        pos = nl + 1;
        continue;
      }
      if (c0 === 62) {
        let qLen = 0;
        while (pos <= len) {
          if (pos === len && len > bodyS && buf[len - 1] === 10) break;
          nl = pos;
          while (nl < len && buf[nl] !== 10) nl++;
          lEnd = nl;
          if (pos >= lEnd || buf[pos] !== 62) break;
          let ts = pos + 1;
          if (ts < lEnd && buf[ts] === 32) ts++;
          qLen = appendTrimToPara(buf, ts, lEnd, qLen);
          if (pos >= len) { pos = len + 1; break; }
          pos = nl + 1;
        }
        if (qLen === 0) {
          p = hCopyPre(PRE_BQ_EMPTY, p);
        } else {
          p = hCopyPre(PRE_BQ_O, p);
          p = mdInline(PARA_BUF, 0, qLen, p, linkCtx);
          p = hCopyPre(PRE_BQ_C, p);
        }
        continue;
      }
      const isUl = pos + 1 < lEnd && (c0 === 45 || c0 === 42) && buf[pos + 1] === 32;
      const ordPay = isUl || c0 < 48 || c0 > 57 ? -1 : bufMatchOrd(buf, pos, lEnd);
      if (isUl || ordPay !== -1) {
        let startNum = 1;
        if (!isUl) {
          startNum = 0;
          for (let k = pos; k < ordPay - 2; k++) startNum = startNum * 10 + (buf[k] - 48);
        }
        if (isUl) p = hCopyPre(PRE_UL_O, p);
        else if (startNum === 1) p = hCopyPre(PRE_OL_O1, p);
        else {
          const sOpen = `<ol start=\\"${startNum}\\">\\n`;
          for (let k = 0; k < sOpen.length; k++) HBUF[p++] = sOpen.charCodeAt(k);
        }
        let itemLen = -1;
        while (pos <= len) {
          if (pos === len && len > bodyS && buf[len - 1] === 10) break;
          nl = pos;
          while (nl < len && buf[nl] !== 10) nl++;
          lEnd = nl;
          let payS = -1;
          if (isUl) {
            if (pos + 1 < lEnd && (buf[pos] === 45 || buf[pos] === 42) && buf[pos + 1] === 32) payS = pos + 2;
          } else {
            payS = bufMatchOrd(buf, pos, lEnd);
          }
          if (payS !== -1) {
            if (itemLen !== -1) {
              p = hCopyPre(PRE_LI_O, p);
              if (itemLen > 0) p = mdInline(PARA_BUF, 0, itemLen, p, linkCtx);
              p = hCopyPre(PRE_LI_C, p);
            }
            itemLen = appendTrimToPara(buf, payS, lEnd, 0);
          } else if (itemLen !== -1 && bufIsContinued(buf, pos, lEnd)) {
            itemLen = appendTrimToPara(buf, pos, lEnd, itemLen);
          } else {
            break;
          }
          if (pos >= len) { pos = len + 1; break; }
          pos = nl + 1;
        }
        if (itemLen !== -1) {
          p = hCopyPre(PRE_LI_O, p);
          if (itemLen > 0) p = mdInline(PARA_BUF, 0, itemLen, p, linkCtx);
          p = hCopyPre(PRE_LI_C, p);
        }
        p = hCopyPre(isUl ? PRE_UL_C : PRE_OL_C, p);
        continue;
      }
    }

    // Zero-Copy Paragraph!
    const paraStart = pos;
    let prevEnd = lEnd;
    const last0 = lEnd > pos ? buf[lEnd - 1] : 0;
    let dirty = c0 === 32 || c0 === 9 || last0 === 32 || last0 === 9;
    pos = nl + 1;

    while (pos <= len) {
      if (pos === len && len > bodyS && buf[len - 1] === 10) break;
      nl = pos;
      while (nl < len && buf[nl] !== 10) nl++;
      lEnd = nl;
      if (bufEndsPara(buf, pos, lEnd)) break;
      if (!dirty) {
        const fc = buf[pos];
        const lc = buf[lEnd - 1];
        if (fc === 32 || fc === 9 || lc === 32 || lc === 9) dirty = true;
      }
      prevEnd = lEnd;
      if (pos >= len) { pos = len + 1; break; }
      pos = nl + 1;
    }

    const dstP = HBUF;
    dstP[p++] = 60; dstP[p++] = 112; dstP[p++] = 62; // <p>
    const inlStart = p;
    if (!dirty) {
      p = mdInline(buf, paraStart, prevEnd, p, linkCtx);
    } else {
      let pLen = 0;
      let p2 = paraStart;
      let firstLine = true;
      while (p2 <= prevEnd) {
        let n2 = p2;
        while (n2 < prevEnd && buf[n2] !== 10) n2++;
        const le2 = n2;
        while (p2 < le2 && (buf[p2] === 32 || buf[p2] === 9)) p2++;
        let e2 = le2;
        while (e2 > p2 && (buf[e2 - 1] === 32 || buf[e2 - 1] === 9)) e2--;
        const subN = e2 - p2;
        const pb = ensureParaBuf(pLen + subN + 2);
        if (firstLine) firstLine = false;
        else pb[pLen++] = 10;
        if (subN > 0) {
          if (subN <= 40) {
            for (let k = p2; k < e2; k++) pb[pLen++] = buf[k];
          } else {
            buf.copy(pb, pLen, p2, e2);
            pLen += subN;
          }
        }
        if (n2 >= prevEnd) break;
        p2 = n2 + 1;
      }
      p = mdInline(PARA_BUF, 0, pLen, p, linkCtx);
    }
    if (exLen === -1) {
      exOff = inlStart;
      exLen = p - inlStart;
    }
    const dstE = HBUF;
    dstE[p++] = 60; dstE[p++] = 47; dstE[p++] = 112; dstE[p++] = 62; dstE[p++] = 92; dstE[p++] = 110; // </p>\n
  }

  return {
    hp: p,
    contentOff: hpStart,
    contentLen: p - hpStart,
    excerptOff: exLen === -1 ? hpStart : exOff,
    excerptLen: exLen === -1 ? 0 : exLen,
  };
}

// ---------------------------------------------------------------------------
// Template AST Parser, Include Inliner, Constant Folder & Bytecode Compiler
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
    if (open === -1 || open === src.length - 1) { text += src.slice(i); break; }
    const next = src[open + 1];
    if (next !== '{' && next !== '%') { text += src.slice(i, open + 1); i = open + 1; continue; }
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
        body.push(node); stack.push(node); body = node.body;
      } else if ((m = IF_RE.exec(tag)) !== null) {
        const node = { kind: 'if', not: m[1] !== undefined, path: tplPathOf(name, m[2]), then: [], else: null };
        body.push(node); stack.push(node); body = node.then;
      } else if (tag === 'else') {
        if (top.kind !== 'if' || top.else !== null) throw new TemplateError(`template "${name}": an else outside an if`);
        top.else = []; body = top.else;
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
      out.push({ kind: 'if', not: n.not, path: n.path, then: inlineAstIncludes(n.then, tplMap, depth), else: n.else === null ? null : inlineAstIncludes(n.else, tplMap, depth) });
    } else if (n.kind === 'for') {
      out.push({ kind: 'for', name: n.name, path: n.path, body: inlineAstIncludes(n.body, tplMap, depth) });
    } else out.push(n);
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
      inner.add(n.name); inner.add('loop');
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
        const br = truthy(lookupDynamic(scope, n.path)) !== n.not ? n.then : n.else;
        if (br !== null) out += renderDynamicPlain(br, scope);
        break;
      }
      case 'for': {
        const xs = lookupDynamic(scope, n.path);
        if (!Array.isArray(xs)) break;
        const len = xs.length;
        for (let k = 0; k < len; k++) {
          out += renderDynamicPlain(n.body, { vars: { [n.name]: xs[k], loop: { index: k + 1, first: k === 0, last: k === len - 1, length: len } }, parent: scope });
        }
        break;
      }
    }
  }
  return out;
}

function pushFoldTxt(folded, txt) {
  if (txt === '') return;
  if (folded.length > 0 && folded[folded.length - 1].kind === 'text') folded[folded.length - 1].text += txt;
  else folded.push({ kind: 'text', text: txt });
}

function foldInvariantNodes(nodes, siteScope) {
  const folded = [];
  for (let i = 0; i < nodes.length; i++) {
    const n = nodes[i];
    if (n.kind === 'text') pushFoldTxt(folded, n.text);
    else if (n.kind === 'var' || n.kind === 'raw') {
      if (INVARIANT_ROOTS.has(n.path[0])) {
        const val = textOf(lookupDynamic(siteScope, n.path));
        pushFoldTxt(folded, n.kind === 'var' ? escHtmlPlain(val) : val);
      } else folded.push(n);
    } else if (n.kind === 'if') {
      if (INVARIANT_ROOTS.has(n.path[0])) {
        const br = truthy(lookupDynamic(siteScope, n.path)) !== n.not ? n.then : n.else;
        if (br !== null) {
          for (const ch of foldInvariantNodes(br, siteScope)) {
            if (ch.kind === 'text') pushFoldTxt(folded, ch.text);
            else folded.push(ch);
          }
        }
      } else {
        folded.push({ kind: 'if', not: n.not, path: n.path, then: foldInvariantNodes(n.then, siteScope), else: n.else === null ? null : foldInvariantNodes(n.else, siteScope) });
      }
    } else if (n.kind === 'for') {
      if (isSiteInvariant(freeVarsOfNodes([n], new Set(), new Set()))) {
        pushFoldTxt(folded, renderDynamicPlain([n], siteScope));
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

const PAGE_SLOTS = { title: 0, url: 1, date: 2, date_long: 3, summary: 4, slug: 5, excerpt: 6, content: 7 };
const TAG_SLOTS = { name: 0, slug: 1, url: 2 };
const PAGER_SLOTS = { url: 0, newer_url: 1, older_url: 2 };

function compileTemplateVm(nodes, tplKind, hpBox) {
  const ops = [];
  let needsDynScope = false;

  const storeChunkH = (rawTxt) => {
    const esc = escJsonStr(rawTxt);
    const maxB = esc.length * 3 + 16;
    ensureHBuf(hpBox.hp + maxB, hpBox.hp);
    const off = hpBox.hp;
    const len = HBUF.utf8Write(esc, off);
    hpBox.hp = off + len;
    return [off, len];
  };

  function resolvePath(path, env) {
    const r = path[0];
    const b = env.get(r);
    if (b === undefined) {
      if (r === 'page' || r === 'posts' || r === 'pager' || r === 'tag') return { missing: true };
      return null;
    }
    if (b.kind === 'loop') {
      if (path.length === 1) return { alwaysTrue: true };
      if (path.length === 2) {
        const f = path[1];
        if (f === 'index') return { kind: 'int', src: 4, reg: b.d, slot: 0, cKind: 6, cReg: b.d, cSlot: 0 };
        if (f === 'length') return { kind: 'int', src: 5, reg: b.d, slot: 0, cKind: 6, cReg: b.d, cSlot: 1 };
        if (f === 'first') return { kind: 'bool', src: 1, reg: b.d, slot: 0, cKind: 6, cReg: b.d, cSlot: 2 };
        if (f === 'last') return { kind: 'bool', src: 2, reg: b.d, slot: 0, cKind: 6, cReg: b.d, cSlot: 3 };
      }
      return null;
    }
    if (b.kind === 'page' || b.kind === 'card') {
      if (path.length === 1) return { alwaysTrue: true };
      if (path.length === 2) {
        const f = path[1];
        if (f === 'title' || f === 'url' || f === 'date' || f === 'date_long' || f === 'summary' || (f === 'slug' && b.kind === 'page')) {
          const sl = PAGE_SLOTS[f];
          return { kind: 'str', rawOnly: false, src: 0, reg: b.reg, slot: sl, cKind: 0, cReg: b.reg, cSlot: sl };
        }
        if (f === 'excerpt' || (f === 'content' && b.kind === 'page')) {
          const sl = PAGE_SLOTS[f];
          return { kind: 'str', rawOnly: true, src: 0, reg: b.reg, slot: sl, cKind: 0, cReg: b.reg, cSlot: sl };
        }
        if (f === 'reading_minutes') return { kind: 'int', src: 0, reg: b.reg, slot: 0, cKind: 2, cReg: b.reg, cSlot: 1 };
        if (f === 'is_post' && b.kind === 'page') return { kind: 'bool', src: 0, reg: b.reg, slot: 0, cKind: 2, cReg: b.reg, cSlot: 0 };
        if (f === 'tags') return { arrKind: 2, arrReg: b.reg, cKind: 2, cReg: b.reg, cSlot: 2 };
        if (f === 'toc' && b.kind === 'page') return { arrKind: 3, arrReg: b.reg, cKind: 2, cReg: b.reg, cSlot: 3 };
        if ((f === 'newer' || f === 'older') && b.kind === 'page') {
          return { cKind: 1, cReg: b.reg, cSlot: (f === 'older' ? 16 : 0) | 15 };
        }
      } else if (path.length === 3 && b.kind === 'page' && (path[1] === 'newer' || path[1] === 'older')) {
        const nb = path[1];
        const f = path[2];
        if (f === 'title' || f === 'url' || f === 'date' || f === 'date_long') {
          const sl = PAGE_SLOTS[f];
          return { kind: 'str', rawOnly: false, src: nb === 'newer' ? 1 : 2, reg: b.reg, slot: sl, cKind: 1, cReg: b.reg, cSlot: (nb === 'older' ? 16 : 0) | sl };
        }
      }
    }
    if (b.kind === 'tagObj' || b.kind === 'tagItem') {
      if (path.length === 1) return { alwaysTrue: true };
      if (path.length === 2) {
        const f = path[1];
        if (f === 'name' || f === 'slug' || f === 'url') {
          const sl = TAG_SLOTS[f];
          return { kind: 'str', rawOnly: false, src: 3, reg: b.reg, slot: sl, cKind: 3, cReg: b.reg, cSlot: sl };
        }
        if (f === 'count') return { kind: 'int', src: 1, reg: b.reg, slot: 0, cKind: 3, cReg: b.reg, cSlot: 3 };
        if (f === 'posts' && b.kind === 'tagObj') return { arrKind: 1, arrReg: b.reg, cKind: 3, cReg: b.reg, cSlot: 4 };
      }
    }
    if (b.kind === 'tocItem') {
      if (path.length === 1) return { alwaysTrue: true };
      if (path.length === 2) {
        const f = path[1];
        if (f === 'level') return { kind: 'int', src: 2, reg: b.reg, slot: 0, cKind: 4, cReg: b.reg, cSlot: 0 };
        if (f === 'id') return { kind: 'str', rawOnly: false, src: 4, reg: b.reg, slot: 0, cKind: 4, cReg: b.reg, cSlot: 1 };
        if (f === 'html') return { kind: 'str', rawOnly: true, src: 4, reg: b.reg, slot: 1, cKind: 4, cReg: b.reg, cSlot: 2 };
      }
    }
    if (b.kind === 'pager') {
      if (path.length === 1) return { alwaysTrue: true };
      if (path.length === 2) {
        const f = path[1];
        if (f === 'url' || f === 'newer_url' || f === 'older_url') {
          const sl = PAGER_SLOTS[f];
          return { kind: 'str', rawOnly: false, src: 5, reg: 0, slot: sl, cKind: 5, cReg: 0, cSlot: sl };
        }
        if (f === 'number' || f === 'total') {
          const sl = f === 'number' ? 0 : 1;
          return { kind: 'int', src: 3, reg: 0, slot: sl, cKind: 5, cReg: 0, cSlot: sl === 0 ? 3 : 4 };
        }
      }
    }
    if (b.kind === 'postsArr' && path.length === 1) {
      return { arrKind: 0, arrReg: 0, cKind: 7, cReg: 0, cSlot: 0 };
    }
    return null;
  }

  function emit(nodes, env, depth) {
    if (depth >= 9) { needsDynScope = true; return; }
    for (let i = 0; i < nodes.length; i++) {
      const n = nodes[i];
      if (n.kind === 'text') {
        if (n.text !== '') {
          const [off, len] = storeChunkH(n.text);
          ops.push(OP_LIT, off, len, 0);
        }
      } else if (n.kind === 'var' || n.kind === 'raw') {
        const isRaw = n.kind === 'raw';
        const r = resolvePath(n.path, env);
        if (r && r.missing) continue;
        if (r && r.kind === 'int') { ops.push(OP_INT, r.src, r.reg, r.slot); continue; }
        if (r && r.kind === 'bool') { ops.push(OP_BOOL, r.src, r.reg, r.slot); continue; }
        if (r && r.kind === 'str' && isRaw === r.rawOnly) { ops.push(OP_STR, r.src, r.reg, r.slot); continue; }
        needsDynScope = true;
        return;
      } else if (n.kind === 'if') {
        const r = resolvePath(n.path, env);
        if (r && r.missing) {
          const br = n.not ? n.then : n.else;
          if (br !== null) emit(br, env, depth);
          continue;
        }
        if (r && r.alwaysTrue) {
          const br = !n.not ? n.then : n.else;
          if (br !== null) emit(br, env, depth);
          continue;
        }
        if (!r || r.cKind === undefined) { needsDynScope = true; return; }
        const jIdx = ops.length;
        ops.push(OP_JCOND, r.cKind, (r.cReg << 16) | (r.cSlot << 8) | (n.not ? 1 : 0), 0);
        emit(n.then, env, depth);
        if (needsDynScope) return;
        if (n.else !== null) {
          const jmpIdx = ops.length;
          ops.push(OP_JMP, 0, 0, 0);
          ops[jIdx + 3] = ops.length;
          emit(n.else, env, depth);
          if (needsDynScope) return;
          ops[jmpIdx + 1] = ops.length;
        } else {
          ops[jIdx + 3] = ops.length;
        }
      } else if (n.kind === 'for') {
        const r = resolvePath(n.path, env);
        if (r && r.missing) continue;
        if (!r || r.arrKind === undefined) { needsDynScope = true; return; }
        const itemReg = depth + 1;
        const itemKind = r.arrKind === 0 || r.arrKind === 1 ? 'card' : r.arrKind === 2 ? 'tagItem' : 'tocItem';
        const nextEnv = new Map(env);
        nextEnv.set(n.name, { kind: itemKind, reg: itemReg });
        nextEnv.set('loop', { kind: 'loop', d: depth });

        if (n.cacheCards) {
          const initIdx = ops.length;
          ops.push(OP_FOR_CARDS_INIT, (depth << 8) | r.arrKind, (r.arrReg << 8) | itemReg, 0);
          const checkIp = ops.length;
          ops.push(OP_FOR_CARDS_CHECK, depth, 0, 0);
          emit(n.body, nextEnv, depth + 1);
          if (needsDynScope) return;
          ops.push(OP_FOR_CARDS_NEXT, depth, checkIp, 0);
          const endIp = ops.length;
          ops[initIdx + 3] = endIp;
          ops[checkIp + 2] = endIp;
        } else {
          const initIdx = ops.length;
          ops.push(OP_FOR_INIT, (depth << 8) | r.arrKind, (r.arrReg << 8) | itemReg, 0);
          const bodyIp = ops.length;
          emit(n.body, nextEnv, depth + 1);
          if (needsDynScope) return;
          ops.push(OP_FOR_NEXT, depth, bodyIp, 0);
          ops[initIdx + 3] = ops.length;
        }
      }
    }
  }

  const rootEnv = new Map();
  if (tplKind === 'page') rootEnv.set('page', { kind: 'page', reg: 0 });
  else if (tplKind === 'index') { rootEnv.set('posts', { kind: 'postsArr', reg: 0 }); rootEnv.set('pager', { kind: 'pager', reg: 0 }); }
  else if (tplKind === 'tag') rootEnv.set('tag', { kind: 'tagObj', reg: 0 });

  emit(nodes, rootEnv, 0);
  if (needsDynScope) return { needsDynScope: true, nodes };
  return { needsDynScope: false, ops: Int32Array.from(ops), nWords: ops.length };
}

// ---------------------------------------------------------------------------
// Raw-UTF8 JSON Cases Streamer (Zero JSON.parse on .md/.static contents!)
// ---------------------------------------------------------------------------
function skipWs(buf, i, len) {
  while (i < len) {
    const b = buf[i];
    if (b === 32 || b === 9 || b === 10 || b === 13) i++;
    else break;
  }
  return i;
}

function skipJsonVal(buf, lat, i, len) {
  i = skipWs(buf, i, len);
  const b = buf[i];
  if (b === 34) return findStrEnd(lat, i + 1) + 1;
  if (b === 123 || b === 91) {
    let depth = 1;
    i++;
    while (i < len && depth > 0) {
      const c = buf[i];
      if (c === 34) {
        i = findStrEnd(lat, i + 1) + 1;
      } else if (c === 123 || c === 91) {
        depth++; i++;
      } else if (c === 125 || c === 93) {
        depth--; i++;
      } else {
        i++;
      }
    }
    return i;
  }
  while (i < len) {
    const c = buf[i];
    if (c === 44 || c === 125 || c === 93 || c === 32 || c === 9 || c === 10 || c === 13) break;
    i++;
  }
  return i;
}

function decodeJsonStrSpan(buf, lat, s, e) {
  const esc = lat.indexOf('\\', s);
  if (esc === -1 || esc >= e) return buf.toString('utf8', s, e);
  return JSON.parse(buf.toString('utf8', s - 1, e + 1));
}

function parseFilesRaw(buf, lat, i, len) {
  i = skipWs(buf, i, len); // '['
  i++;
  const files = [];
  while (i < len) {
    i = skipWs(buf, i, len);
    if (buf[i] === 93) { i++; break; }
    if (buf[i] === 44) { i++; i = skipWs(buf, i, len); }
    // '{'
    i++;
    let pathStr = '';
    let cs = 0, ce = 0;
    while (i < len) {
      i = skipWs(buf, i, len);
      if (buf[i] === 125) { i++; break; }
      if (buf[i] === 44) { i++; i = skipWs(buf, i, len); }
      const ks = i + 1;
      const ke = findStrEnd(lat, ks);
      const kl = ke - ks;
      i = skipWs(buf, ke + 1, len); // ':'
      i = skipWs(buf, i + 1, len);
      if (kl === 4 && buf[ks] === 112 && buf[ks + 1] === 97 && buf[ks + 2] === 116 && buf[ks + 3] === 104) {
        const vs = i + 1;
        const ve = findStrEnd(lat, vs);
        pathStr = decodeJsonStrSpan(buf, lat, vs, ve);
        i = ve + 1;
      } else if (kl === 7 && buf[ks] === 99 && buf[ks + 1] === 111 && buf[ks + 2] === 110 && buf[ks + 3] === 116 && buf[ks + 4] === 101 && buf[ks + 5] === 110 && buf[ks + 6] === 116) {
        const vs = i + 1;
        const ve = findStrEnd(lat, vs);
        cs = vs; ce = ve;
        i = ve + 1;
      } else {
        i = skipJsonVal(buf, lat, i, len);
      }
    }
    files.push({ path: pathStr, rawS: cs, rawE: ce, isMd: pathStr.endsWith('.md'), jsContent: null });
  }
  return [files, i];
}

function parseInputObjRaw(buf, lat, i, len) {
  i = skipWs(buf, i, len); // '{'
  i++;
  let site = null, templates = null, files = null;
  while (i < len) {
    i = skipWs(buf, i, len);
    if (buf[i] === 125) { i++; break; }
    if (buf[i] === 44) { i++; i = skipWs(buf, i, len); }
    const ks = i + 1;
    const ke = findStrEnd(lat, ks);
    const key = buf.toString('latin1', ks, ke);
    i = skipWs(buf, ke + 1, len); // ':'
    i = skipWs(buf, i + 1, len);
    if (key === 'site' || key === 'templates') {
      const vs = i;
      const ve = skipJsonVal(buf, lat, vs, len);
      const obj = JSON.parse(buf.toString('utf8', vs, ve));
      if (key === 'site') site = obj; else templates = obj;
      i = ve;
    } else if (key === 'files') {
      const res = parseFilesRaw(buf, lat, i, len);
      files = res[0];
      i = res[1];
    } else {
      i = skipJsonVal(buf, lat, i, len);
    }
  }
  return [{ site, templates, files }, i];
}

function parseCasesRaw(buf, lat) {
  const len = buf.length;
  let i = skipWs(buf, 0, len); // '['
  i++;
  const out = [];
  while (i < len) {
    i = skipWs(buf, i, len);
    if (buf[i] === 93) break;
    if (buf[i] === 44) { i++; i = skipWs(buf, i, len); }
    // case object '{'
    i++;
    let inp = null;
    while (i < len) {
      i = skipWs(buf, i, len);
      if (buf[i] === 125) { i++; break; }
      if (buf[i] === 44) { i++; i = skipWs(buf, i, len); }
      const ks = i + 1;
      const ke = findStrEnd(lat, ks);
      const key = buf.toString('latin1', ks, ke);
      i = skipWs(buf, ke + 1, len); // ':'
      i = skipWs(buf, i + 1, len);
      if (key === 'input') {
        const res = parseInputObjRaw(buf, lat, i, len);
        inp = res[0];
        i = res[1];
      } else {
        i = skipJsonVal(buf, lat, i, len);
      }
    }
    out.push(inp);
  }
  return out;
}

// ---------------------------------------------------------------------------
// Core Site Builder -> streams straight into OUT_SLAB
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

const dirOf = (p) => (p.includes('/') ? p.slice(0, p.lastIndexOf('/')) : '');

function buildSiteToOutSlab(inp, rawBuf, op) {
  const S = VM_S;
  const hpBox = { hp: 0 };
  S.cp = 0;

  const allocFieldH = (str) => {
    if (str === '') return [0, 0];
    const esc = escHtmlJsonStr(str);
    const maxB = esc.length * 3 + 16;
    ensureHBuf(hpBox.hp + maxB, hpBox.hp);
    const off = hpBox.hp;
    const len = HBUF.utf8Write(esc, off);
    hpBox.hp = off + len;
    return [off, len];
  };

  const rawTpls = new Map();
  const report = [];
  const tplNames = Object.keys(inp.templates).sort(byCodeUnits);
  for (let i = 0; i < tplNames.length; i++) {
    const name = tplNames[i];
    try {
      rawTpls.set(name, parseTemplateAst(name, inp.templates[name]));
    } catch (err) {
      if (!(err instanceof TemplateError)) throw err;
      report.push(err.message);
    }
  }

  const mdSources = [];
  const statics = [];
  const rawFiles = inp.files;
  for (let i = 0; i < rawFiles.length; i++) {
    const f = rawFiles[i];
    if (f.isMd) mdSources.push(f);
    else statics.push(f);
  }
  mdSources.sort((a, b) => byCodeUnits(a.path, b.path));
  statics.sort((a, b) => byCodeUnits(a.path, b.path));

  const base = inp.site.base_url.replace(/\/+$/, '');
  const siteVar = { title: inp.site.title, base_url: base };

  // Decode raw JSON string span of a .md file into MD_BUF once, parse frontmatter, save body coords!
  const kept = [];
  const bySource = new Map();
  const takenMap = new Map();
  const slugCache = new Map();
  const cachedSlug = (name) => {
    let sl = slugCache.get(name);
    if (sl === undefined) { sl = slugifyStr(name); slugCache.set(name, sl); }
    return sl;
  };

  let bp = 0;

  // Pass 1: Unescape each .md ONCE into BODY_SLAB; validate frontmatter; retain body span for kept files!
  for (let i = 0; i < mdSources.length; i++) {
    const src = mdSources[i];
    const fileStart = bp;
    let mdLen;
    if (rawBuf !== null) {
      const spanLen = src.rawE - src.rawS;
      const bs = ensureBodySlab(fileStart + spanLen + 16, fileStart);
      mdLen = K_unescMd(rawBuf, src.rawS, src.rawE, bs, fileStart, UNESC_TBL);
      if (mdLen === -1) {
        const sNorm = JSON.parse(rawBuf.toString('utf8', src.rawS - 1, src.rawE + 1)).replace(/\r\n?/g, '\n');
        const bNeed = Buffer.byteLength(sNorm, 'utf8') + 16;
        mdLen = ensureBodySlab(fileStart + bNeed, fileStart).utf8Write(sNorm, fileStart);
      }
    } else {
      const sNorm = src.jsContent.indexOf('\r') === -1 ? src.jsContent : src.jsContent.replace(/\r\n?/g, '\n');
      const bNeed = Buffer.byteLength(sNorm, 'utf8') + 16;
      mdLen = ensureBodySlab(fileStart + bNeed, fileStart).utf8Write(sNorm, fileStart);
    }

    const fileEnd = fileStart + mdLen;
    const fm = parseFrontMatterBuf(BODY_SLAB, fileStart, fileEnd);
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
    if (post && fm.data.date === '') {
      report.push(`refused ${src.path}: a post needs a date`);
      continue;
    }
    const layout = fm.data.layout !== '' ? fm.data.layout : (post ? 'post' : 'page');
    if (!rawTpls.has(layout)) {
      report.push(`refused ${src.path}: layout "${layout}" is no template that parses`);
      continue;
    }
    if (fm.data.draft === true) {
      report.push(`draft ${src.path}`);
      continue;
    }

    bp = fileEnd;
    const dir = post ? 'posts' : dirOf(src.path);
    let tSet = takenMap.get(dir);
    if (tSet === undefined) {
      tSet = new Set(dir === '' ? RESERVED : undefined);
      takenMap.set(dir, tSet);
    }
    const slug = uniqueSlug(fm.data.slug !== '' ? fm.data.slug : slugifyStr(fm.data.title), tSet);
    const outDir = dir === '' ? slug : `${dir}/${slug}`;
    const url = `${base}/${outDir}/`;
    const item = {
      pid: kept.length,
      src,
      data: fm.data,
      post,
      layout,
      slug,
      outDir,
      url,
      newerPid: -1,
      olderPid: -1,
      bodyStart: fm.bodyStart,
      bodyEnd: fileEnd,
    };
    kept.push(item);
    bySource.set(src.path, item);
  }

  ensurePageCap(kept.length + 1);
  const staticSet = new Set();
  for (let i = 0; i < statics.length; i++) staticSet.add(statics[i].path);

  const broken = new Set();
  const dirPartsCache = new Map();
  const linkCtx = { warm: 0, dirParts: [], bySource, staticSet, broken, base, srcPath: '' };
  const tocOut = { count: 0 };

  // Pass 2: Render Markdown directly from BODY_SLAB into HBUF & count words in one pass!
  for (let i = 0; i < kept.length; i++) {
    const it = kept[i];
    const pid = it.pid;
    const src = it.src;
    const dir = dirOf(src.path);
    let dirParts = dirPartsCache.get(dir);
    if (dirParts === undefined) {
      dirParts = dir === '' ? [] : dir.split('/');
      dirPartsCache.set(dir, dirParts);
    }
    linkCtx.dirParts = dirParts;
    linkCtx.srcPath = src.path;

    const bS = it.bodyStart;
    const bE = it.bodyEnd;
    S.pTocStart[pid] = tocOut.count;
    const mdRes = renderMarkdownIntoHBuf(BODY_SLAB, bS, bE, hpBox.hp, linkCtx, tocOut);
    hpBox.hp = mdRes.hp;
    S.pTocCount[pid] = tocOut.count - S.pTocStart[pid];

    const words = K_wordsU8(BODY_SLAB, bS, bE, WS_TBL);
    S.pReadMin[pid] = Math.max(1, Math.ceil(words / 200));
    S.pIsPost[pid] = it.post ? 1 : 0;

    const pBase = pid * PF_STRIDE;
    const d = it.data;
    const [tO, tL] = allocFieldH(d.title); S.pOff[pBase] = tO; S.pLen[pBase] = tL;
    const [uO, uL] = allocFieldH(it.url); S.pOff[pBase + 1] = uO; S.pLen[pBase + 1] = uL;
    const [dO, dL] = allocFieldH(d.date); S.pOff[pBase + 2] = dO; S.pLen[pBase + 2] = dL;
    const dl = d.date === '' ? '' : longDate(d.date);
    const [dlO, dlL] = allocFieldH(dl); S.pOff[pBase + 3] = dlO; S.pLen[pBase + 3] = dlL;
    const [sO, sL] = allocFieldH(d.summary); S.pOff[pBase + 4] = sO; S.pLen[pBase + 4] = sL;
    const [slO, slL] = allocFieldH(it.slug); S.pOff[pBase + 5] = slO; S.pLen[pBase + 5] = slL;
    S.pOff[pBase + 6] = mdRes.excerptOff; S.pLen[pBase + 6] = mdRes.excerptLen;
    S.pOff[pBase + 7] = mdRes.contentOff; S.pLen[pBase + 7] = mdRes.contentLen;
    it.dateLong = dl;
  }

  // Posts sort, newer/older links
  const posts = kept.filter((s) => s.post);
  posts.sort((x, y) => byCodeUnits(y.data.date, x.data.date) || byCodeUnits(x.slug, y.slug));
  for (let k = 0; k < posts.length; k++) {
    const p = posts[k];
    S.postPids[k] = p.pid;
    S.pCid[p.pid] = k;
    S.cardLen[k] = -1;
    const nPid = k === 0 ? -1 : posts[k - 1].pid;
    const oPid = k === posts.length - 1 ? -1 : posts[k + 1].pid;
    p.newerPid = nPid; p.olderPid = oPid;
    S.pNewer[p.pid] = nPid;
    S.pOlder[p.pid] = oPid;
  }

  // Tags & page tags
  const byTagSlug = new Map();
  const allTagsList = []; // includes post tags and missing-page tags!
  const missingTagMap = new Map();
  const ownTags = (s) => {
    const arr = s.data.tags;
    if (arr === null || arr.length === 0) return [];
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
    p.tids = new Array(ot.length);
    for (let k = 0; k < ot.length; k++) {
      const [name, sl] = ot[k];
      let tObj = byTagSlug.get(sl);
      if (tObj === undefined) {
        tObj = { tid: -1, name, slug: sl, url: `${base}/tags/${sl}/`, posts: [] };
        byTagSlug.set(sl, tObj);
      }
      tObj.posts.push(p);
      p.tids[k] = tObj;
    }
  }
  const realTags = [...byTagSlug.values()].sort((x, y) => y.posts.length - x.posts.length || byCodeUnits(x.slug, y.slug));
  for (let i = 0; i < realTags.length; i++) {
    realTags[i].tid = allTagsList.length;
    allTagsList.push(realTags[i]);
  }
  for (let i = 0; i < kept.length; i++) {
    const s = kept[i];
    if (!s.post) {
      const ot = ownTags(s);
      s.tids = new Array(ot.length);
      for (let k = 0; k < ot.length; k++) {
        const [name, sl] = ot[k];
        let tObj = byTagSlug.get(sl);
        if (tObj === undefined) {
          const ck = sl + '\0' + name;
          tObj = missingTagMap.get(ck);
          if (tObj === undefined) {
            tObj = { tid: allTagsList.length, name, slug: sl, url: '', posts: null };
            missingTagMap.set(ck, tObj);
            allTagsList.push(tObj);
          }
        }
        s.tids[k] = tObj;
      }
    }
  }

  ensureTagCap(allTagsList.length + 1);
  let tagPostCursor = 0;
  for (let i = 0; i < allTagsList.length; i++) {
    const t = allTagsList[i];
    const tb = i * TF_STRIDE;
    const [nO, nL] = allocFieldH(t.name); S.tOff[tb] = nO; S.tLen[tb] = nL;
    const [sO, sL] = allocFieldH(t.slug); S.tOff[tb + 1] = sO; S.tLen[tb + 1] = sL;
    const [uO, uL] = allocFieldH(t.url); S.tOff[tb + 2] = uO; S.tLen[tb + 2] = uL;
    if (t.posts !== null) {
      S.tCount[i] = t.posts.length;
      S.tPostStart[i] = tagPostCursor;
      S.tPostCount[i] = t.posts.length;
      ensureAllTagPostsCap(tagPostCursor + t.posts.length);
      for (let k = 0; k < t.posts.length; k++) S.allTagPosts[tagPostCursor++] = t.posts[k].pid;
    } else {
      S.tCount[i] = 0;
      S.tPostStart[i] = 0;
      S.tPostCount[i] = 0;
    }
  }

  let pageTagCursor = 0;
  for (let i = 0; i < kept.length; i++) {
    const s = kept[i];
    const pid = s.pid;
    S.pTagStart[pid] = pageTagCursor;
    S.pTagCount[pid] = s.tids.length;
    ensureAllPageTagsCap(pageTagCursor + s.tids.length);
    for (let k = 0; k < s.tids.length; k++) S.allPageTags[pageTagCursor++] = s.tids[k].tid;
  }

  // Build lightweight siteScope for template folding (and lazy dynamic fallback only if needed)
  const tagCardsDyn = realTags.map((t) => ({ name: t.name, slug: t.slug, url: t.url, count: t.posts.length }));
  const decodeHPlain = (off, len) => {
    if (len <= 0) return '';
    const s = HBUF.toString('utf8', off, off + len);
    return s.indexOf('\\') === -1 ? s : JSON.parse('"' + s + '"');
  };
  const makeDynCard = (it) => {
    const pb = it.pid * PF_STRIDE;
    return {
      title: it.data.title, url: it.url, date: it.data.date, date_long: it.dateLong,
      summary: it.data.summary, excerpt: decodeHPlain(S.pOff[pb + 6], S.pLen[pb + 6]),
      reading_minutes: S.pReadMin[it.pid],
      tags: it.tids.map((t) => t.posts !== null ? { name: t.name, slug: t.slug, url: t.url, count: t.posts.length } : { name: t.name, slug: t.slug, url: '' }),
    };
  };
  const recentDyn = posts.slice(0, inp.site.recent).map(makeDynCard);
  const siteScope = { vars: { site: siteVar, tags: tagCardsDyn, recent: recentDyn }, parent: null };

  const compiledTpls = new Map();
  const getCompiled = (name, kind) => {
    const ck = name + ':' + kind;
    let c = compiledTpls.get(ck);
    if (c === undefined) {
      const raw = rawTpls.get(name);
      if (raw === undefined) { compiledTpls.set(ck, null); return null; }
      const inlined = inlineAstIncludes(raw, rawTpls, 0);
      const folded = foldInvariantNodes(inlined, siteScope);
      c = compileTemplateVm(folded, kind, hpBox);
      compiledTpls.set(ck, c);
    }
    return c;
  };

  // Helper to emit JSON entry into OUT_SLAB
  const writtenKeys = new Set();
  let firstEntry = true;
  const openKv = (kStr, curOp) => {
    writtenKeys.add(kStr);
    let p = curOp;
    const kn = kStr.length;
    const need = p + kn * 6 + 16;
    if (need > OUT_SLAB.length) ensureOutSlab(need, p);
    const outB = OUT_SLAB;
    outB[p++] = firstEntry ? 123 : 44; // '{' or ','
    firstEntry = false;
    outB[p++] = 34;
    let asciiFast = true;
    for (let k = 0; k < kn; k++) {
      const c = kStr.charCodeAt(k);
      if (c < 32 || c > 126 || c === 34 || c === 92) { asciiFast = false; break; }
      outB[p + k] = c;
    }
    if (asciiFast) {
      p += kn;
    } else {
      p = writeOutEscJsonStr(kStr, p);
    }
    OUT_SLAB[p++] = 34; OUT_SLAB[p++] = 58; OUT_SLAB[p++] = 34; // ":"
    return p;
  };
  const closeKv = (curOp) => {
    if (curOp + 4 > OUT_SLAB.length) ensureOutSlab(curOp + 4, curOp);
    OUT_SLAB[curOp++] = 34;
    return curOp;
  };

  const makeDynPage = (it) => {
    const baseCard = makeDynCard(it);
    const pb = it.pid * PF_STRIDE;
    const tS = S.pTocStart[it.pid], tC = S.pTocCount[it.pid];
    const toc = new Array(tC);
    for (let k = 0; k < tC; k++) {
      const tid = tS + k;
      toc[k] = { level: S.tocLevel[tid], id: HBUF.toString('latin1', S.tocIdOff[tid], S.tocIdOff[tid] + S.tocIdLen[tid]), html: decodeHPlain(S.tocHtmlOff[tid], S.tocHtmlLen[tid]) };
    }
    return {
      ...baseCard,
      slug: it.slug,
      content: decodeHPlain(S.pOff[pb + 7], S.pLen[pb + 7]),
      is_post: it.post,
      toc,
      newer: it.newerPid === -1 ? null : { title: kept[it.newerPid].data.title, url: kept[it.newerPid].url, date: kept[it.newerPid].data.date, date_long: kept[it.newerPid].dateLong },
      older: it.olderPid === -1 ? null : { title: kept[it.olderPid].data.title, url: kept[it.olderPid].url, date: kept[it.olderPid].data.date, date_long: kept[it.olderPid].dateLong },
    };
  };

  // Render pages
  for (let i = 0; i < kept.length; i++) {
    const it = kept[i];
    const comp = getCompiled(it.layout, 'page');
    op = openKv(`${it.outDir}/index.html`, op);
    if (!comp.needsDynScope) {
      S.regVal[0] = it.pid;
      op = execVm(comp.ops, comp.nWords, op, S);
    } else {
      const sc = { vars: { site: siteVar, tags: tagCardsDyn, recent: recentDyn, page: makeDynPage(it) }, parent: null };
      op = writeOutEscJsonStr(renderDynamicPlain(comp.nodes, sc), op);
    }
    op = closeKv(op);
  }

  // Render index pages
  const per = inp.site.per_page;
  const pages = Math.max(1, Math.ceil(posts.length / per));
  const indexUrl = (k) => (k === 1 ? `${base}/` : `${base}/page/${k}/`);
  const indexComp = getCompiled('index', 'index');
  if (indexComp !== null) {
    for (let k = 1; k <= pages; k++) {
      const url = indexUrl(k);
      const nUrl = k === 1 ? '' : indexUrl(k - 1);
      const oUrl = k === pages ? '' : indexUrl(k + 1);
      const start = (k - 1) * per;
      const cnt = Math.max(0, Math.min(posts.length, k * per) - start);
      op = openKv(k === 1 ? 'index.html' : `page/${k}/index.html`, op);
      if (!indexComp.needsDynScope) {
        const [uO, uL] = allocFieldH(url); S.pgOff[0] = uO; S.pgLen[0] = uL;
        const [nO, nL] = allocFieldH(nUrl); S.pgOff[1] = nO; S.pgLen[1] = nL;
        const [oO, oL] = allocFieldH(oUrl); S.pgOff[2] = oO; S.pgLen[2] = oL;
        S.pgNumber = k; S.pgTotal = pages;
        S.curPostStart = start; S.curPostLen = cnt;
        op = execVm(indexComp.ops, indexComp.nWords, op, S);
      } else {
        const slPosts = posts.slice(start, start + cnt).map(makeDynCard);
        const pager = { number: k, total: pages, url, newer_url: nUrl, older_url: oUrl };
        const sc = { vars: { site: siteVar, tags: tagCardsDyn, recent: recentDyn, posts: slPosts, pager }, parent: null };
        op = writeOutEscJsonStr(renderDynamicPlain(indexComp.nodes, sc), op);
      }
      op = closeKv(op);
    }
  }

  // Render tag pages
  const tagComp = getCompiled('tag', 'tag');
  if (tagComp !== null) {
    for (let i = 0; i < realTags.length; i++) {
      const tp = realTags[i];
      op = openKv(`tags/${tp.slug}/index.html`, op);
      if (!tagComp.needsDynScope) {
        S.regVal[0] = tp.tid;
        op = execVm(tagComp.ops, tagComp.nWords, op, S);
      } else {
        const tagVar = { name: tp.name, slug: tp.slug, url: tp.url, count: tp.posts.length, posts: tp.posts.map(makeDynCard) };
        const sc = { vars: { site: siteVar, tags: tagCardsDyn, recent: recentDyn, tag: tagVar }, parent: null };
        op = writeOutEscJsonStr(renderDynamicPlain(tagComp.nodes, sc), op);
      }
      op = closeKv(op);
    }
  }

  // Render tags index
  const tagsComp = getCompiled('tags', 'tags');
  if (tagsComp !== null) {
    op = openKv('tags/index.html', op);
    if (!tagsComp.needsDynScope) {
      op = execVm(tagsComp.ops, tagsComp.nWords, op, S);
    } else {
      op = writeOutEscJsonStr(renderDynamicPlain(tagsComp.nodes, siteScope), op);
    }
    op = closeKv(op);
  }

  // Render static files (ZERO-COPY directly from rawBuf!)
  for (let i = 0; i < statics.length; i++) {
    const f = statics[i];
    if (writtenKeys.has(f.path)) {
      report.push(`shadowed ${f.path}: a built page has its path`);
      continue;
    }
    if (f.path === 'build-report.txt') continue;
    op = openKv(f.path, op);
    if (rawBuf !== null) {
      const rLen = f.rawE - f.rawS;
      if (op + rLen + 16 > OUT_SLAB.length) ensureOutSlab(op + rLen + 16, op);
      if (rLen > 0) rawBuf.copy(OUT_SLAB, op, f.rawS, f.rawE);
      op += rLen;
    } else {
      op = writeOutEscJsonStr(f.jsContent, op);
    }
    op = closeKv(op);
  }

  // Build report
  const rLines = [...report, ...broken].sort(byCodeUnits);
  rLines.push(`built ${kept.length - posts.length} pages, ${posts.length} posts, ${realTags.length} tags and ${statics.length} static files`);
  op = openKv('build-report.txt', op);
  op = writeOutEscJsonStr(`${rLines.join('\n')}\n`, op);
  op = closeKv(op);

  if (op + 4 > OUT_SLAB.length) ensureOutSlab(op + 4, op);
  OUT_SLAB[op++] = 125; // '}'
  return op;
}

// Pre-warm ONLY the 3 K_* byte kernels once at load (covering <=40B, >40B, escapes, syntax stops & UTF-8 -> 0 deopts).
(function prewarmByteKernels() {
  const sBuf = Buffer.from('aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab\\n\\r\\n\\r\\t\\b\\f\\"\\\\\\/\\u');
  const dBuf = Buffer.allocUnsafe(128);
  const wBuf = Buffer.concat([
    Buffer.from('  hello world\tfoo\nbar aaaa '),
    Buffer.from([0xC2, 0xA0, 0xC3, 0xA9, 0xE2, 0x80, 0x83, 0xE2, 0x82, 0xAC, 0xF0, 0x9F, 0x98, 0x80, 32, 120]),
  ]);
  const mdWarm = Buffer.from(
    'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa & < > " \' \n \t \r \x01 \\\\ \\* [l] `c` short end'
  );
  for (let i = 0; i < 150; i++) {
    K_unescMd(sBuf, 0, sBuf.length, dBuf, 0, UNESC_TBL);
    K_unescMd(sBuf, 0, sBuf.length, dBuf, 8, UNESC_TBL);
    K_wordsU8(wBuf, 0, wBuf.length, WS_TBL);
    let ki = 0;
    while (ki < mdWarm.length) {
      ki = K_scanEsc(mdWarm, ki, mdWarm.length, HBUF, 0, MD_LUT, HJ_FLAT);
      if (ki < mdWarm.length) ki++;
    }
    K_scanEsc(mdWarm, 0, mdWarm.length, HBUF, 0, HJ_LEN, HJ_FLAT);
  }
})();

function writeFdAll(fd, buf, len) {
  let off = 0;
  while (off < len) off += writeSync(fd, buf, off, len - off);
}

function runFile(inPath, outPath) {
  const rawBuf = readFileSync(inPath);
  const lat = rawBuf.toString('latin1');
  const cases = parseCasesRaw(rawBuf, lat);
  const fd = openSync(outPath, 'w');
  let op = 0;
  OUT_SLAB[op++] = 91; // '['
  for (let i = 0; i < cases.length; i++) {
    if (i > 0) OUT_SLAB[op++] = 44; // ','
    op = buildSiteToOutSlab(cases[i], rawBuf, op);
    cases[i] = null;
    if (i < cases.length - 1 && op > 2 * 1024 * 1024) {
      writeFdAll(fd, OUT_SLAB, op);
      op = 0;
    }
  }
  if (op + 4 > OUT_SLAB.length) ensureOutSlab(op + 4, op);
  OUT_SLAB[op++] = 93; // ']'
  writeFdAll(fd, OUT_SLAB, op);
  closeSync(fd);
}

function run(input) {
  const rawFiles = input.files;
  const files = new Array(rawFiles.length);
  for (let i = 0; i < rawFiles.length; i++) {
    const f = rawFiles[i];
    files[i] = { path: f.path, rawS: 0, rawE: 0, isMd: f.path.endsWith('.md'), jsContent: f.content };
  }
  const op = buildSiteToOutSlab({ site: input.site, templates: input.templates, files }, null, 0);
  return JSON.parse(OUT_SLAB.toString('utf8', 0, op));
}

module.exports = { runFile, run };
