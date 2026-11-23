// sitegen-apex v8: Unified CopyWithin Slab + Frontmatter-First Skip + Branchless 4x WordCount + Flat Bytecode VM
'use strict';

const { openSync, closeSync, fstatSync, readSync, writeSync } = require('node:fs');

// ---------------------------------------------------------------------------
// Unified Pre-Allocated CopyWithin Slab (SLAB + SLAB_BUF share ArrayBuffer)
// Layout in runFile(): [0..rawLen) raw cases.json | [rawLen..bodyEnd) bodies |
// [bodyEnd..pagerBase) HTML/templates | [pagerBase..cardBase) pager scratch |
// [cardBase..outBase) cached post cards | [outBase..) JSON output stream
// ---------------------------------------------------------------------------
let SLAB = new Uint8Array(12 * 1024 * 1024);
let SLAB_BUF = Buffer.from(SLAB.buffer);

function ensureSlab(need, used) {
  if (need <= SLAB.length) return SLAB;
  let cap = SLAB.length;
  while (cap < need) cap *= 2;
  const next = new Uint8Array(cap);
  if (used > 0) next.set(SLAB.subarray(0, used));
  SLAB = next;
  SLAB_BUF = Buffer.from(next.buffer);
  return SLAB;
}

let PARA_BUF = new Uint8Array(64 * 1024);
let PARA_BUF_B = Buffer.from(PARA_BUF.buffer);
function ensureParaBuf(need, curLen) {
  if (need <= PARA_BUF.length) return PARA_BUF;
  let cap = PARA_BUF.length;
  while (cap < need) cap *= 2;
  const next = new Uint8Array(cap);
  if (curLen > 0) next.set(PARA_BUF.subarray(0, curLen));
  PARA_BUF = next;
  PARA_BUF_B = Buffer.from(next.buffer);
  return PARA_BUF;
}

let FM_BUF = new Uint8Array(8 * 1024);
let FM_BUF_B = Buffer.from(FM_BUF.buffer);
function ensureFmBuf(need) {
  if (need <= FM_BUF.length) return FM_BUF;
  let cap = FM_BUF.length;
  while (cap < need) cap *= 2;
  FM_BUF = new Uint8Array(cap);
  FM_BUF_B = Buffer.from(FM_BUF.buffer);
  return FM_BUF;
}

let LINK_BUF = new Uint8Array(8 * 1024);
let LINK_BUF_B = Buffer.from(LINK_BUF.buffer);
function ensureLinkBuf(need) {
  if (need <= LINK_BUF.length) return LINK_BUF;
  let cap = LINK_BUF.length;
  while (cap < need) cap *= 2;
  LINK_BUF = new Uint8Array(cap);
  LINK_BUF_B = Buffer.from(LINK_BUF.buffer);
  return LINK_BUF;
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

// Branchless 4x word-count class: 0 = ASCII WS, 1 = ASCII/UTF8 non-WS, 2 = Unicode WS lead byte
const W_CLS = new Uint8Array(256);
W_CLS.fill(1);
W_CLS[9] = 0; W_CLS[10] = 0; W_CLS[11] = 0; W_CLS[12] = 0; W_CLS[13] = 0; W_CLS[32] = 0;
W_CLS[0xC2] = 2; W_CLS[0xE1] = 2; W_CLS[0xE2] = 2; W_CLS[0xE3] = 2; W_CLS[0xEF] = 2;

const BLK_START = new Uint8Array(256);
BLK_START[9] = 1; BLK_START[32] = 1; BLK_START[35] = 1; BLK_START[42] = 1;
BLK_START[45] = 1; BLK_START[62] = 1; BLK_START[96] = 1;
for (let c = 48; c <= 57; c++) BLK_START[c] = 1;

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

function slugifyStr(text, uCache = null) {
  const n = text.length;
  for (let i = 0; i < n; i++) {
    if (text.charCodeAt(i) >= 128) return slugifyUnicode(text, uCache);
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

function slugifyBuf(buf, s, e, uCache = null) {
  for (let i = s; i < e; i++) {
    if (buf[i] >= 128) {
      const b = buf === SLAB ? SLAB_BUF : Buffer.from(buf.buffer, buf.byteOffset, buf.byteLength);
      return slugifyUnicode(b.toString('utf8', s, e), uCache);
    }
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

function slugifyUnicode(text, uCache) {
  if (uCache !== null) {
    const hit = uCache.get(text);
    if (hit !== undefined) return hit;
  }
  const plain = text.normalize('NFKD').replace(/\p{M}/gu, '');
  let outLen = 0;
  let gap = false;
  const n = plain.length;
  for (let i = 0; i < n; i++) {
    const c = plain.charCodeAt(i);
    const mapped = c < 128 ? SLUG_TBL[c] : 0;
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
  const res = outLen === 0 ? 'untitled' : SLUG_SCRATCH.toString('latin1', 0, outLen);
  if (uCache !== null) uCache.set(text, res);
  return res;
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
// Core Byte Kernels (Latin1 SIMD + CopyWithin Slab + Branchless 4x WordCount)
// ---------------------------------------------------------------------------

// Unescape JSON string [s..e) into slab[dp..], normalizing \r\n and \r -> \n.
// Uses latin1 indexOf('\\') + copyWithin; returns -1 on \uXXXX or unknown escape.
function K_unescIdxOfCW(slab, lat, s, e, dp, tbl) {
  let i = s | 0;
  let p = dp | 0;
  const end = e | 0;
  while (i < end) {
    const bs = lat.indexOf('\\', i);
    const segEnd = (bs === -1 || bs >= end) ? end : bs;
    const n = segEnd - i;
    if (n > 0) {
      if (n <= 40) {
        for (let k = i; k < segEnd; k++) slab[p++] = slab[k];
      } else {
        slab.copyWithin(p, i, segEnd);
        p += n;
      }
    }
    if (segEnd >= end) break;
    if (segEnd + 1 >= end) return -1;
    const c = slab[segEnd + 1];
    const m = tbl[c];
    if (m !== 0) {
      slab[p++] = m;
      i = segEnd + 2;
    } else if (c === 114) {
      slab[p++] = 10;
      i = segEnd + 2;
      if (i + 1 < end && slab[i] === 92 && slab[i + 1] === 110) i += 2;
    } else {
      return -1;
    }
  }
  return p - dp;
}

// Small separate-buffer unescape for frontmatter [s..e) into FM_BUF[0..].
function unescSmall(src, s, e, dst, tbl) {
  let i = s | 0;
  let p = 0;
  const end = e | 0;
  while (i < end) {
    const b = src[i];
    if (b === 92) {
      if (i + 1 >= end) return -1;
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
  return p;
}

let FM_RAW_BODY_S = 0;
// Locate closing '---' of frontmatter directly in JSON-escaped raw SLAB (only when !hasAnyU).
// Returns fmRawEnd (>= 0) and sets FM_RAW_BODY_S, or -2 (no front matter), or -3 (not closed).
function findRawFmEnd(slab, lat, rawS, rawE) {
  const rLen = rawE - rawS;
  if (rLen < 3 || slab[rawS] !== 45 || slab[rawS + 1] !== 45 || slab[rawS + 2] !== 45) return -2;
  let scan;
  if (rLen === 3) return -3;
  if (slab[rawS + 3] === 92 && rawS + 4 < rawE) {
    const c1 = slab[rawS + 4];
    if (c1 === 110) {
      scan = rawS + 5;
    } else if (c1 === 114) {
      scan = (rawS + 6 < rawE && slab[rawS + 5] === 92 && slab[rawS + 6] === 110) ? rawS + 7 : rawS + 5;
    } else {
      return -2;
    }
  } else {
    return -2;
  }
  let idx = lat.indexOf('---', scan);
  while (idx !== -1 && idx + 3 <= rawE) {
    if (idx >= rawS + 2 && slab[idx - 2] === 92 && (slab[idx - 1] === 110 || slab[idx - 1] === 114)) {
      let bs = idx - 2;
      while (bs >= rawS && slab[bs] === 92) bs--;
      if (((idx - 2 - bs) & 1) === 1) {
        const after = idx + 3;
        if (after === rawE) {
          FM_RAW_BODY_S = rawE;
          return after;
        }
        if (slab[after] === 92 && after + 1 < rawE) {
          const nc = slab[after + 1];
          if (nc === 110) {
            FM_RAW_BODY_S = after + 2;
            return after;
          }
          if (nc === 114) {
            FM_RAW_BODY_S = (after + 3 < rawE && slab[after + 2] === 92 && slab[after + 3] === 110) ? after + 4 : after + 2;
            return after;
          }
        }
      }
    }
    idx = lat.indexOf('---', idx + 1);
  }
  return -3;
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

// Branchless 4x-unrolled UTF-8 word counter matching JS String(/\S+/g) exact rules.
function K_words4(buf, s, e, cls) {
  let words = 0;
  let prev = 0;
  let i = s | 0;
  const end = e | 0;
  const end4 = end - 3;
  while (i < end) {
    while (i < end4) {
      const t0 = cls[buf[i]];
      const t1 = cls[buf[i + 1]];
      const t2 = cls[buf[i + 2]];
      const t3 = cls[buf[i + 3]];
      if ((t0 | t1 | t2 | t3) >= 2) break;
      words += (t0 & (prev ^ 1)) + (t1 & (t0 ^ 1)) + (t2 & (t1 ^ 1)) + (t3 & (t2 ^ 1));
      prev = t3;
      i += 4;
    }
    if (i >= end) break;
    const t = cls[buf[i]];
    if (t < 2) {
      words += t & (prev ^ 1);
      prev = t;
      i++;
    } else {
      const r = nonAsciiWsStep(buf, i, end);
      if (r > 0) {
        prev = 0;
        i = r;
      } else {
        words += (prev ^ 1);
        prev = 1;
        i = -r;
      }
    }
  }
  return words;
}

// Fast scanner + HTML/JSON escaper using copyWithin inside unified SLAB (stops on lut[b]===1).
const SCAN_P = new Int32Array(1);
function K_scanEsc(src, s, e, dst, p, lut, flat) {
  let i = s | 0;
  const end = e | 0;
  let op = p | 0;
  const same = src === dst;
  while (i < end) {
    const st = i;
    while (i < end && lut[src[i]] === 0) i++;
    const n = i - st;
    if (n > 0) {
      if (n <= 40) {
        for (let k = st; k < i; k++) dst[op++] = src[k];
      } else if (same) {
        dst.copyWithin(op, st, i);
        op += n;
      } else {
        dst.set(src.subarray(st, i), op);
        op += n;
      }
    }
    if (i >= end) break;
    const ch = src[i];
    const code = lut[ch];
    if (code === 1) break;
    const off = ch << 3;
    for (let k = 0; k < code; k++) dst[op++] = flat[off + k];
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
  const srcIsSlab = src === SLAB;
  const c0 = src[hs];
  if (c0 === 47 || c0 === 35 || isSchemeBuf(src, hs, he)) {
    const need = p + (he - hs) * 6 + remEnd * 6 + 65536;
    if (need > SLAB.length) ensureSlab(need, p);
    K_scanEsc(srcIsSlab ? SLAB : src, hs, he, SLAB, p, HJ_LEN, HJ_FLAT);
    return SCAN_P[0];
  }
  const srcB = srcIsSlab ? SLAB_BUF : (src === PARA_BUF ? PARA_BUF_B : Buffer.from(src.buffer, src.byteOffset, src.byteLength));
  const target = srcB.toString('utf8', hs, he);
  const hash = target.indexOf('#');
  const rel = hash === -1 ? target : target.slice(0, hash);
  let out = null;
  if (rel !== '') {
    let up = 0, rOff = 0;
    const rn = rel.length;
    while (rOff + 2 < rn && rel.charCodeAt(rOff) === 46 && rel.charCodeAt(rOff + 1) === 46 && rel.charCodeAt(rOff + 2) === 47) {
      up++;
      rOff += 3;
    }
    const upPre = ctx.upPrefix;
    if (up < upPre.length && rOff < rn && rel.charCodeAt(rOff) !== 46 && rel.charCodeAt(rOff) !== 47 &&
        rel.charCodeAt(rn - 1) !== 47 && rel.indexOf('/.', rOff) === -1 && rel.indexOf('//', rOff) === -1) {
      out = upPre[up] + (rOff === 0 ? rel : rel.slice(rOff));
    } else {
      out = resolveRelPathParts(ctx.dirParts, rel);
    }
  }
  let resolved;
  if (out !== null) {
    const hit = ctx.bySource.get(out);
    if (hit !== undefined) {
      const pIdx = hit.pid * PF_STRIDE + 1;
      const uOff = VM_S.pOff[pIdx];
      const uLen = VM_S.pLen[pIdx];
      const need = p + uLen + (he - hs) * 6 + remEnd * 6 + 65536;
      if (need > SLAB.length) ensureSlab(need, p);
      const sl = SLAB;
      if (uLen <= 40) {
        for (let k = 0; k < uLen; k++) sl[p++] = sl[uOff + k];
      } else {
        sl.copyWithin(p, uOff, uOff + uLen);
        p += uLen;
      }
      if (hash !== -1) {
        let hb = hs;
        const curSrc = srcIsSlab ? sl : src;
        while (hb < he && curSrc[hb] !== 35) hb++;
        K_scanEsc(curSrc, hb, he, sl, p, HJ_LEN, HJ_FLAT);
        p = SCAN_P[0];
      }
      return p;
    } else if (ctx.staticSet.has(out)) {
      resolved = ctx.base + '/' + out + (hash === -1 ? '' : target.slice(hash));
    } else {
      ctx.broken.add('broken-link ' + ctx.srcPath + ' -> ' + target);
      resolved = target;
    }
  } else {
    ctx.broken.add('broken-link ' + ctx.srcPath + ' -> ' + target);
    resolved = target;
  }
  const lb = ensureLinkBuf(resolved.length * 3 + 16);
  const nb = LINK_BUF_B.utf8Write(resolved, 0);
  const need = p + nb * 6 + remEnd * 6 + 65536;
  if (need > SLAB.length) ensureSlab(need, p);
  K_scanEsc(lb, 0, nb, SLAB, p, HJ_LEN, HJ_FLAT);
  return SCAN_P[0];
}

// Single-pass Byte-Native Inline Markdown using K_scanEsc.
function mdInline(src, s, e, p, ctx) {
  let i = s | 0;
  const end = e | 0;
  const srcIsSlab = src === SLAB;
  while (i < end) {
    let curSrc = srcIsSlab ? SLAB : src;
    i = K_scanEsc(curSrc, i, end, SLAB, p, MD_LUT, HJ_FLAT);
    p = SCAN_P[0];
    if (i >= end) break;
    let dst = SLAB;
    curSrc = srcIsSlab ? dst : src;
    const ch = curSrc[i];
    if (ch === 92) {
      if (i + 1 < end) {
        const nc = curSrc[i + 1];
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
      while (j < end && curSrc[j] !== 96) j++;
      if (j < end && j > i + 1) {
        dst[p++] = 60; dst[p++] = 99; dst[p++] = 111; dst[p++] = 100; dst[p++] = 101; dst[p++] = 62; // <code>
        K_scanEsc(curSrc, i + 1, j, dst, p, HJ_LEN, HJ_FLAT);
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
      if (i + 1 < end && curSrc[i + 1] === 42) {
        const j = findUnescapedDStarBuf(curSrc, i + 2, end);
        if (j > i + 2) {
          dst[p++] = 60; dst[p++] = 115; dst[p++] = 116; dst[p++] = 114; dst[p++] = 111; dst[p++] = 110; dst[p++] = 103; dst[p++] = 62; // <strong>
          p = mdInline(curSrc, i + 2, j, p, ctx);
          dst = SLAB;
          dst[p++] = 60; dst[p++] = 47; dst[p++] = 115; dst[p++] = 116; dst[p++] = 114; dst[p++] = 111; dst[p++] = 110; dst[p++] = 103; dst[p++] = 62; // </strong>
          i = j + 2;
        } else {
          dst[p++] = 42; dst[p++] = 42;
          i += 2;
        }
      } else {
        const j = findSingleStarBuf(curSrc, i + 1, end);
        if (j > i + 1) {
          dst[p++] = 60; dst[p++] = 101; dst[p++] = 109; dst[p++] = 62; // <em>
          p = mdInline(curSrc, i + 1, j, p, ctx);
          dst = SLAB;
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
    const k = findUnescapedCharBuf(curSrc, 93, i + 1, end);
    if (k !== -1 && k + 1 < end && curSrc[k + 1] === 40) {
      let m = k + 2;
      while (m < end && curSrc[m] !== 41) m++;
      if (m < end && m > k + 2 && !hasBufWhitespace(curSrc, k + 2, m)) {
        dst[p++] = 60; dst[p++] = 97; dst[p++] = 32; dst[p++] = 104; dst[p++] = 114; dst[p++] = 101; dst[p++] = 102; dst[p++] = 61; dst[p++] = 92; dst[p++] = 34; // <a href=\"
        p = writeResolvedHref(curSrc, k + 2, m, end - m, p, ctx);
        dst = SLAB;
        dst[p++] = 92; dst[p++] = 34; dst[p++] = 62; // \">
        p = mdInline(srcIsSlab ? dst : curSrc, i + 1, k, p, ctx);
        dst = SLAB;
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
  if (op + maxB > SLAB.length) ensureSlab(op + maxB, op);
  return op + SLAB_BUF.utf8Write(escaped, op);
}

function writeOutUint(n, op) {
  const dst = op + 16 > SLAB.length ? ensureSlab(op + 16, op) : SLAB;
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
  cardLimit: 0,
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
  let sl = SLAB;
  let slCap = sl.length;
  while (ip < nWords) {
    const code = ops[ip];
    const a1 = ops[ip + 1];
    const a2 = ops[ip + 2];
    const a3 = ops[ip + 3];
    ip += 4;
    if (code === OP_LIT) {
      if (a2 > 0) {
        if (op + a2 + 64 > slCap) { sl = ensureSlab(op + a2 + 64, op); slCap = sl.length; }
        if (a2 <= 40) {
          const end = a1 + a2;
          for (let k = a1; k < end; k++) sl[op++] = sl[k];
        } else {
          sl.copyWithin(op, a1, a1 + a2);
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
        if (op + sLen + 64 > slCap) { sl = ensureSlab(op + sLen + 64, op); slCap = sl.length; }
        if (sLen <= 40) {
          const end = sOff + sLen;
          for (let k = sOff; k < end; k++) sl[op++] = sl[k];
        } else {
          sl.copyWithin(op, sOff, sOff + sLen);
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
        if (op + 16 > slCap) { sl = ensureSlab(op + 64, op); slCap = sl.length; }
        if (val < 10) {
          sl[op++] = 48 + val;
        } else if (val < 100) {
          const q = (val / 10) | 0;
          sl[op++] = 48 + q;
          sl[op++] = 48 + (val - q * 10);
        } else {
          op = writeOutUint(val, op);
          sl = SLAB; slCap = sl.length;
        }
      }
    } else if (code === OP_BOOL) {
      let bv;
      if (a1 === 0) bv = S.pIsPost[S.regVal[a2]] !== 0;
      else if (a1 === 1) bv = S.loopIdx[a2] === 1;
      else bv = S.loopIdx[a2] === S.loopLen[a2];
      if (op + 8 > slCap) { sl = ensureSlab(op + 64, op); slCap = sl.length; }
      if (bv) { sl[op++] = 116; sl[op++] = 114; sl[op++] = 117; sl[op++] = 101; }
      else { sl[op++] = 102; sl[op++] = 97; sl[op++] = 108; sl[op++] = 115; sl[op++] = 101; }
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
          if (op + cLen + 64 > slCap) { sl = ensureSlab(op + cLen + 64, op); slCap = sl.length; }
          const off = S.cardOff[cid];
          if (cLen <= 40) {
            const end = off + cLen;
            for (let k = off; k < end; k++) sl[op++] = sl[k];
          } else {
            sl.copyWithin(op, off, off + cLen);
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
        const cp = S.cp;
        if (cp + cLen <= S.cardLimit) {
          sl.copyWithin(cp, cs, op);
          S.cardOff[cid] = cp;
          S.cardLen[cid] = cLen;
          S.cp = cp + cLen;
        }
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

let FM_ERR_Q = '';
function parseQuotedFmBuf(buf, bufB, s, e) {
  if (e - s < 2 || buf[e - 1] !== 34) { FM_ERR_Q = 'a quoted string is not closed'; return null; }
  const innerS = s + 1;
  const innerE = e - 1;
  let hasSpecial = false;
  for (let i = innerS; i < innerE; i++) {
    if (buf[i] === 92 || buf[i] === 34) { hasSpecial = true; break; }
  }
  if (!hasSpecial) return bufB.toString('utf8', innerS, innerE);
  let p = 0;
  const out = LINK_BUF.length < (innerE - innerS) ? ensureLinkBuf(innerE - innerS) : LINK_BUF;
  for (let i = innerS; i < innerE; i++) {
    const c = buf[i];
    if (c === 92) {
      if (i + 1 >= innerE) { FM_ERR_Q = 'a quoted string holds an escape other than \\" or \\\\'; return null; }
      const n = buf[i + 1];
      if (n !== 34 && n !== 92) { FM_ERR_Q = 'a quoted string holds an escape other than \\" or \\\\'; return null; }
      out[p++] = n;
      i++;
    } else if (c === 34) {
      FM_ERR_Q = 'a quoted string holds a stray quote';
      return null;
    } else {
      out[p++] = c;
    }
  }
  return LINK_BUF_B.toString('utf8', 0, p);
}

function fmBufEq(buf, s, e, lit) {
  const n = lit.length;
  if (e - s !== n) return false;
  for (let i = 0; i < n; i++) if (buf[s + i] !== lit.charCodeAt(i)) return false;
  return true;
}

const KEY_NAMES = ['title', 'date', 'tags', 'draft', 'layout', 'slug', 'summary'];
const FM_RES = { title: '', date: '', summary: '', layout: '', slug: '', draft: false, tags: null, err: '', bodyStart: 0 };

function parseFrontMatterBuf(buf, bufB, basePos, endLimit) {
  const len = endLimit;
  const fm = FM_RES;
  let nl = basePos;
  while (nl < len && buf[nl] !== 10) nl++;
  if (nl - basePos !== 3 || buf[basePos] !== 45 || buf[basePos + 1] !== 45 || buf[basePos + 2] !== 45) {
    fm.err = 'no front matter';
    return false;
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
  if (closePos === -1) { fm.err = 'the front matter is not closed'; return false; }

  fm.title = ''; fm.date = ''; fm.summary = ''; fm.layout = ''; fm.slug = ''; fm.draft = false; fm.tags = null;
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
      if (colon === -1 || colon === pos) { fm.err = `line ${idx + 1} is not "key: value"`; return false; }
      for (let k = pos; k < colon; k++) {
        const b = buf[k];
        if (!((b >= 97 && b <= 122) || b === 95)) { fm.err = `line ${idx + 1} is not "key: value"`; return false; }
      }
      if (colon + 1 < lEnd && buf[colon + 1] !== 32) { fm.err = `line ${idx + 1} is not "key: value"`; return false; }
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
      else { fm.err = `unknown key "${bufB.toString('utf8', pos, colon)}"`; return false; }

      const bit = 1 << kid;
      if ((seenMask & bit) !== 0) { fm.err = `key "${KEY_NAMES[kid]}" is given twice`; return false; }
      seenMask |= bit;
      if (vs >= ve) { fm.err = `key "${KEY_NAMES[kid]}" has no value`; return false; }

      if (kid === 0 || kid === 6) {
        const b0 = buf[vs];
        let val;
        if (b0 === 34) {
          val = parseQuotedFmBuf(buf, bufB, vs, ve);
          if (val === null) { fm.err = `key "${KEY_NAMES[kid]}": ${FM_ERR_Q}`; return false; }
        } else if (b0 === 91) {
          fm.err = `key "${KEY_NAMES[kid]}": a bare string opens on [`;
          return false;
        } else {
          val = bufB.toString('utf8', vs, ve);
        }
        if (kid === 0) fm.title = val;
        else fm.summary = val;
      } else if (kid === 1) {
        if (!isValidDateBuf(buf, vs, ve)) { fm.err = 'key "date": not a date from 1970-01-01 to 2099-12-31 (YYYY-MM-DD)'; return false; }
        fm.date = bufB.toString('latin1', vs, ve);
      } else if (kid === 3) {
        if (fmBufEq(buf, vs, ve, 'true')) fm.draft = true;
        else if (fmBufEq(buf, vs, ve, 'false')) fm.draft = false;
        else { fm.err = 'key "draft": true or false'; return false; }
      } else if (kid === 4) {
        for (let k = vs; k < ve; k++) {
          const c = buf[k];
          if (!((c >= 97 && c <= 122) || (c >= 48 && c <= 57) || c === 45)) { fm.err = 'key "layout": not a template name'; return false; }
        }
        fm.layout = bufB.toString('latin1', vs, ve);
      } else if (kid === 5) {
        if (ve - vs > SLUG_MAX || buf[vs] === 45 || buf[ve - 1] === 45) { fm.err = 'key "slug": not a slug'; return false; }
        for (let k = vs; k < ve; k++) {
          const c = buf[k];
          const ok = (c >= 97 && c <= 122) || (c >= 48 && c <= 57) || (c === 45 && buf[k - 1] !== 45);
          if (!ok) { fm.err = 'key "slug": not a slug'; return false; }
        }
        fm.slug = bufB.toString('latin1', vs, ve);
      } else {
        if (buf[vs] !== 91 || buf[ve - 1] !== 93) { fm.err = 'key "tags": not a list [a, b]'; return false; }
        const rawT = bufB.toString('utf8', vs + 1, ve - 1);
        if (rawT.trim() === '') fm.tags = [];
        else {
          const tags = rawT.split(',').map((t) => t.trim());
          for (let ti = 0; ti < tags.length; ti++) {
            const tg = tags[ti];
            if (tg === '' || tg.includes('"') || tg.includes('[') || tg.includes(']')) {
              fm.err = 'key "tags": an empty tag, or one holding " [ or ]';
              return false;
            }
          }
          fm.tags = tags;
        }
      }
    }
    idx++;
    pos = lEnd + 1;
  }
  if ((seenMask & 1) === 0) { fm.err = 'no title'; return false; }
  fm.bodyStart = bodyStart >= len ? len : bodyStart;
  return true;
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
  const pb = ensureParaBuf(pLen + n + 2, pLen);
  if (pLen > 0) pb[pLen++] = 10;
  if (n <= 40) {
    for (let k = s; k < e; k++) pb[pLen++] = buf[k];
  } else {
    pb.set(buf.subarray(s, e), pLen);
    pLen += n;
  }
  return pLen;
}

function hCopyPre(pre, p) {
  const n = pre.length;
  const dst = SLAB;
  for (let k = 0; k < n; k++) dst[p++] = pre[k];
  return p;
}

const MD_RES = { hp: 0, contentOff: 0, contentLen: 0, excerptOff: 0, excerptLen: 0 };
const REUSABLE_HIDS = new Set();

function renderMarkdownIntoHBuf(bodyLat, bodyBase, bodyS, bodyE, hpStart, linkCtx, tocOut) {
  REUSABLE_HIDS.clear();
  let p = hpStart;
  const needBase = p + (bodyE - bodyS) * 10 + 262144;
  if (needBase > SLAB.length) ensureSlab(needBase, p);
  let sl = SLAB;

  let pos = bodyS;
  let exOff = 0, exLen = -1;
  const len = bodyE;
  const blkTbl = BLK_START;

  while (pos <= len) {
    if (pos === len && len > bodyS && sl[len - 1] === 10) break;
    if (p + 65536 > sl.length) sl = ensureSlab(p + (len - pos) * 10 + 262144, p);
    let rel = bodyLat.indexOf('\n', pos - bodyBase);
    let nl = rel === -1 ? len : bodyBase + rel;
    if (nl > len) nl = len;
    let lEnd = nl;
    const c0 = pos < lEnd ? sl[pos] : -1;

    if (c0 === -1) {
      if (pos >= len) break;
      pos = nl + 1;
      continue;
    }

    if (blkTbl[c0] === 1) {
      if ((c0 === 32 || c0 === 9) && bufIsBlank(sl, pos, lEnd)) {
        if (pos >= len) break;
        pos = nl + 1;
        continue;
      }
      if (c0 === 96) {
        const langEnd = bufFenceOpen(sl, pos, lEnd);
        if (langEnd !== -1) {
          p = hCopyPre(PRE_FENCE_O, p);
          if (langEnd > pos + 3) {
            p = hCopyPre(PRE_FENCE_LANG, p);
            K_scanEsc(sl, pos + 3, langEnd, sl, p, HJ_LEN, HJ_FLAT);
            p = SCAN_P[0];
            sl[p++] = 92; sl[p++] = 34; // \"
          }
          sl[p++] = 62; // >
          pos = nl + 1;
          while (pos <= len) {
            if (p + 65536 > sl.length) sl = ensureSlab(p + (len - pos) * 10 + 262144, p);
            rel = bodyLat.indexOf('\n', pos - bodyBase);
            nl = rel === -1 ? len : bodyBase + rel;
            if (nl > len) nl = len;
            lEnd = nl;
            if (bufFenceClose(sl, pos, lEnd)) {
              pos = nl + 1;
              break;
            }
            if (lEnd > pos) {
              K_scanEsc(sl, pos, lEnd, sl, p, HJ_LEN, HJ_FLAT);
              p = SCAN_P[0];
            }
            sl[p++] = 92; sl[p++] = 110; // \n
            if (pos >= len) { pos = len + 1; break; }
            pos = nl + 1;
          }
          p = hCopyPre(PRE_FENCE_C, p);
          continue;
        }
      }
      if (c0 === 35 && bufHeading(sl, pos, lEnd)) {
        const d = _bHd;
        const id = uniqueSlug(slugifyBuf(sl, _bHs, _bHe, linkCtx.uCache), REUSABLE_HIDS);
        sl[p++] = 60; sl[p++] = 104; sl[p++] = 48 + d;
        sl[p++] = 32; sl[p++] = 105; sl[p++] = 100; sl[p++] = 61; sl[p++] = 92; sl[p++] = 34;
        const idOff = p;
        for (let k = 0; k < id.length; k++) sl[p++] = id.charCodeAt(k);
        const idLen = p - idOff;
        sl[p++] = 92; sl[p++] = 34; sl[p++] = 62;
        const hInlStart = p;
        p = mdInline(sl, _bHs, _bHe, p, linkCtx);
        sl = SLAB;
        const hInlLen = p - hInlStart;
        sl[p++] = 60; sl[p++] = 47; sl[p++] = 104; sl[p++] = 48 + d; sl[p++] = 62; sl[p++] = 92; sl[p++] = 110;
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
      if ((c0 === 45 || c0 === 42) && bufIsHr(sl, pos, lEnd)) {
        p = hCopyPre(PRE_HR, p);
        if (pos >= len) break;
        pos = nl + 1;
        continue;
      }
      if (c0 === 62) {
        let qLen = 0;
        while (pos <= len) {
          if (pos === len && len > bodyS && sl[len - 1] === 10) break;
          rel = bodyLat.indexOf('\n', pos - bodyBase);
          nl = rel === -1 ? len : bodyBase + rel;
          if (nl > len) nl = len;
          lEnd = nl;
          if (pos >= lEnd || sl[pos] !== 62) break;
          let ts = pos + 1;
          if (ts < lEnd && sl[ts] === 32) ts++;
          qLen = appendTrimToPara(sl, ts, lEnd, qLen);
          if (pos >= len) { pos = len + 1; break; }
          pos = nl + 1;
        }
        if (qLen === 0) {
          p = hCopyPre(PRE_BQ_EMPTY, p);
        } else {
          p = hCopyPre(PRE_BQ_O, p);
          p = mdInline(PARA_BUF, 0, qLen, p, linkCtx);
          sl = SLAB;
          p = hCopyPre(PRE_BQ_C, p);
        }
        continue;
      }
      const isUl = pos + 1 < lEnd && (c0 === 45 || c0 === 42) && sl[pos + 1] === 32;
      const ordPay = isUl || c0 < 48 || c0 > 57 ? -1 : bufMatchOrd(sl, pos, lEnd);
      if (isUl || ordPay !== -1) {
        let startNum = 1;
        if (!isUl) {
          startNum = 0;
          for (let k = pos; k < ordPay - 2; k++) startNum = startNum * 10 + (sl[k] - 48);
        }
        if (isUl) p = hCopyPre(PRE_UL_O, p);
        else if (startNum === 1) p = hCopyPre(PRE_OL_O1, p);
        else {
          const sOpen = `<ol start=\\"${startNum}\\">\\n`;
          for (let k = 0; k < sOpen.length; k++) sl[p++] = sOpen.charCodeAt(k);
        }
        let itemLen = -1;
        while (pos <= len) {
          if (pos === len && len > bodyS && sl[len - 1] === 10) break;
          rel = bodyLat.indexOf('\n', pos - bodyBase);
          nl = rel === -1 ? len : bodyBase + rel;
          if (nl > len) nl = len;
          lEnd = nl;
          let payS = -1;
          if (isUl) {
            if (pos + 1 < lEnd && (sl[pos] === 45 || sl[pos] === 42) && sl[pos + 1] === 32) payS = pos + 2;
          } else {
            payS = bufMatchOrd(sl, pos, lEnd);
          }
          if (payS !== -1) {
            if (itemLen !== -1) {
              p = hCopyPre(PRE_LI_O, p);
              if (itemLen > 0) {
                if (p + itemLen * 10 + 65536 > sl.length) sl = ensureSlab(p + itemLen * 10 + 262144, p);
                p = mdInline(PARA_BUF, 0, itemLen, p, linkCtx);
                sl = SLAB;
              }
              p = hCopyPre(PRE_LI_C, p);
            }
            itemLen = appendTrimToPara(sl, payS, lEnd, 0);
          } else if (itemLen !== -1 && bufIsContinued(sl, pos, lEnd)) {
            itemLen = appendTrimToPara(sl, pos, lEnd, itemLen);
          } else {
            break;
          }
          if (pos >= len) { pos = len + 1; break; }
          pos = nl + 1;
        }
        if (itemLen !== -1) {
          p = hCopyPre(PRE_LI_O, p);
          if (itemLen > 0) {
            if (p + itemLen * 10 + 65536 > sl.length) sl = ensureSlab(p + itemLen * 10 + 262144, p);
            p = mdInline(PARA_BUF, 0, itemLen, p, linkCtx);
            sl = SLAB;
          }
          p = hCopyPre(PRE_LI_C, p);
        }
        p = hCopyPre(isUl ? PRE_UL_C : PRE_OL_C, p);
        continue;
      }
    }

    // Zero-Copy Paragraph!
    const paraStart = pos;
    let prevEnd = lEnd;
    const last0 = lEnd > pos ? sl[lEnd - 1] : 0;
    let dirty = c0 === 32 || c0 === 9 || last0 === 32 || last0 === 9;
    pos = nl + 1;

    while (pos <= len) {
      if (pos === len && len > bodyS && sl[len - 1] === 10) break;
      rel = bodyLat.indexOf('\n', pos - bodyBase);
      nl = rel === -1 ? len : bodyBase + rel;
      if (nl > len) nl = len;
      lEnd = nl;
      if (bufEndsPara(sl, pos, lEnd)) break;
      if (!dirty) {
        const fc = sl[pos];
        const lc = sl[lEnd - 1];
        if (fc === 32 || fc === 9 || lc === 32 || lc === 9) dirty = true;
      }
      prevEnd = lEnd;
      if (pos >= len) { pos = len + 1; break; }
      pos = nl + 1;
    }

    sl[p++] = 60; sl[p++] = 112; sl[p++] = 62; // <p>
    const inlStart = p;
    if (!dirty) {
      p = mdInline(sl, paraStart, prevEnd, p, linkCtx);
      sl = SLAB;
    } else {
      let pLen = 0;
      let p2 = paraStart;
      let firstLine = true;
      while (p2 <= prevEnd) {
        let rel2 = bodyLat.indexOf('\n', p2 - bodyBase);
        let n2 = rel2 === -1 ? prevEnd : bodyBase + rel2;
        if (n2 > prevEnd) n2 = prevEnd;
        const le2 = n2;
        while (p2 < le2 && (sl[p2] === 32 || sl[p2] === 9)) p2++;
        let e2 = le2;
        while (e2 > p2 && (sl[e2 - 1] === 32 || sl[e2 - 1] === 9)) e2--;
        const subN = e2 - p2;
        const pb = ensureParaBuf(pLen + subN + 2, pLen);
        if (firstLine) firstLine = false;
        else pb[pLen++] = 10;
        if (subN > 0) {
          if (subN <= 40) {
            for (let k = p2; k < e2; k++) pb[pLen++] = sl[k];
          } else {
            pb.set(sl.subarray(p2, e2), pLen);
            pLen += subN;
          }
        }
        if (n2 >= prevEnd) break;
        p2 = n2 + 1;
      }
      p = mdInline(PARA_BUF, 0, pLen, p, linkCtx);
      sl = SLAB;
    }
    if (exLen === -1) {
      exOff = inlStart;
      exLen = p - inlStart;
    }
    sl[p++] = 60; sl[p++] = 47; sl[p++] = 112; sl[p++] = 62; sl[p++] = 92; sl[p++] = 110; // </p>\n
  }

  MD_RES.hp = p;
  MD_RES.contentOff = hpStart;
  MD_RES.contentLen = p - hpStart;
  MD_RES.excerptOff = exLen === -1 ? hpStart : exOff;
  MD_RES.excerptLen = exLen === -1 ? 0 : exLen;
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
    ensureSlab(hpBox.hp + maxB, hpBox.hp);
    const off = hpBox.hp;
    const len = SLAB_BUF.utf8Write(esc, off);
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

function decodeJsonStrSpan(bufB, lat, s, e) {
  const esc = lat.indexOf('\\', s);
  if (esc === -1 || esc >= e) return bufB.toString('utf8', s, e);
  return JSON.parse(bufB.toString('utf8', s - 1, e + 1));
}

function parseFilesRaw(buf, bufB, lat, i, len) {
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
        pathStr = decodeJsonStrSpan(bufB, lat, vs, ve);
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

function parseInputObjRaw(buf, bufB, lat, i, len) {
  i = skipWs(buf, i, len); // '{'
  i++;
  let site = null, templates = null, files = null;
  while (i < len) {
    i = skipWs(buf, i, len);
    if (buf[i] === 125) { i++; break; }
    if (buf[i] === 44) { i++; i = skipWs(buf, i, len); }
    const ks = i + 1;
    const ke = findStrEnd(lat, ks);
    const key = bufB.toString('latin1', ks, ke);
    i = skipWs(buf, ke + 1, len); // ':'
    i = skipWs(buf, i + 1, len);
    if (key === 'site' || key === 'templates') {
      const vs = i;
      const ve = skipJsonVal(buf, lat, vs, len);
      const obj = JSON.parse(bufB.toString('utf8', vs, ve));
      if (key === 'site') site = obj; else templates = obj;
      i = ve;
    } else if (key === 'files') {
      const res = parseFilesRaw(buf, bufB, lat, i, len);
      files = res[0];
      i = res[1];
    } else {
      i = skipJsonVal(buf, lat, i, len);
    }
  }
  return [{ site, templates, files }, i];
}

function parseCasesRaw(buf, bufB, lat, len) {
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
      const key = bufB.toString('latin1', ks, ke);
      i = skipWs(buf, ke + 1, len); // ':'
      i = skipWs(buf, i + 1, len);
      if (key === 'input') {
        const res = parseInputObjRaw(buf, bufB, lat, i, len);
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

const OWN_TAG_SEEN = new Set();

function writeSlotFieldH(str, offArr, lenArr, slotIdx, hpBox) {
  const n = str.length;
  if (n === 0) {
    offArr[slotIdx] = 0;
    lenArr[slotIdx] = 0;
    return;
  }
  const hp = hpBox.hp;
  const maxB = n * 6 + 16;
  const h = hp + maxB > SLAB.length ? ensureSlab(hp + maxB, hp) : SLAB;
  const hj = HJ_LEN;
  let asciiClean = true;
  for (let i = 0; i < n; i++) {
    const c = str.charCodeAt(i);
    if (c >= 128 || hj[c] !== 0) { asciiClean = false; break; }
    h[hp + i] = c;
  }
  if (asciiClean) {
    offArr[slotIdx] = hp;
    lenArr[slotIdx] = n;
    hpBox.hp = hp + n;
    return;
  }
  const esc = escHtmlJsonStr(str);
  const escMax = esc.length * 3 + 16;
  if (hp + escMax > SLAB.length) ensureSlab(hp + escMax, hp);
  const len = SLAB_BUF.utf8Write(esc, hp);
  offArr[slotIdx] = hp;
  lenArr[slotIdx] = len;
  hpBox.hp = hp + len;
}

function cachedSlug(name, slugCache, uCache) {
  let sl = slugCache.get(name);
  if (sl === undefined) { sl = slugifyStr(name, uCache); slugCache.set(name, sl); }
  return sl;
}

function openKv(kStr, op, writtenKeys, sepByte) {
  writtenKeys.add(kStr);
  const kn = kStr.length;
  const need = op + kn * 6 + 16;
  const outB = need > SLAB.length ? ensureSlab(need, op) : SLAB;
  outB[op++] = sepByte;
  outB[op++] = 34;
  let asciiFast = true;
  for (let k = 0; k < kn; k++) {
    const c = kStr.charCodeAt(k);
    if (c < 32 || c > 126 || c === 34 || c === 92) { asciiFast = false; break; }
    outB[op + k] = c;
  }
  if (asciiFast) {
    op += kn;
  } else {
    op = writeOutEscJsonStr(kStr, op);
  }
  if (op + 4 > SLAB.length) ensureSlab(op + 4, op);
  SLAB[op++] = 34; SLAB[op++] = 58; SLAB[op++] = 34; // ":"
  return op;
}

function closeKv(op) {
  const dst = op + 4 > SLAB.length ? ensureSlab(op + 4, op) : SLAB;
  dst[op++] = 34;
  return op;
}

function decodeHPlain(off, len) {
  if (len <= 0) return '';
  const s = SLAB_BUF.toString('utf8', off, off + len);
  return s.indexOf('\\') === -1 ? s : JSON.parse('"' + s + '"');
}

function makeDynCard(it, S) {
  const pb = it.pid * PF_STRIDE;
  return {
    title: it.title, url: it.url, date: it.date, date_long: it.dateLong,
    summary: it.summary, excerpt: decodeHPlain(S.pOff[pb + 6], S.pLen[pb + 6]),
    reading_minutes: S.pReadMin[it.pid],
    tags: it.tObjs.map((t) => t.posts !== null ? { name: t.name, slug: t.slug, url: t.url, count: t.posts.length } : { name: t.name, slug: t.slug, url: '' }),
  };
}

function makeDynPage(it, kept, S) {
  const baseCard = makeDynCard(it, S);
  const pb = it.pid * PF_STRIDE;
  const tS = S.pTocStart[it.pid], tC = S.pTocCount[it.pid];
  const toc = new Array(tC);
  for (let k = 0; k < tC; k++) {
    const tid = tS + k;
    toc[k] = { level: S.tocLevel[tid], id: SLAB_BUF.toString('latin1', S.tocIdOff[tid], S.tocIdOff[tid] + S.tocIdLen[tid]), html: decodeHPlain(S.tocHtmlOff[tid], S.tocHtmlLen[tid]) };
  }
  return {
    ...baseCard,
    slug: it.slug,
    content: decodeHPlain(S.pOff[pb + 7], S.pLen[pb + 7]),
    is_post: it.post,
    toc,
    newer: it.newerPid === -1 ? null : { title: kept[it.newerPid].title, url: kept[it.newerPid].url, date: kept[it.newerPid].date, date_long: kept[it.newerPid].dateLong },
    older: it.olderPid === -1 ? null : { title: kept[it.olderPid].title, url: kept[it.olderPid].url, date: kept[it.olderPid].date, date_long: kept[it.olderPid].dateLong },
  };
}

function getCompiledTpl(name, kind, rawTpls, compiledTpls, siteScope, hpBox) {
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
}

function buildSiteToOutSlab(inp, rawLen, rawLat, hasAnyU, prefixByte, isLast, outRange) {
  const S = VM_S;

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

  const bodyBase = rawLen;
  let sumMdRaw = 0;
  if (rawLen > 0) {
    for (let i = 0; i < mdSources.length; i++) sumMdRaw += mdSources[i].rawE - mdSources[i].rawS;
  } else {
    for (let i = 0; i < mdSources.length; i++) sumMdRaw += mdSources[i].jsContent.length * 3 + 16;
  }
  ensureSlab(bodyBase + sumMdRaw + 65536, bodyBase);

  const kept = [];
  const bySource = new Map();
  const takenMap = new Map();
  const slugCache = new Map();
  const uCache = new Map();
  const fm = FM_RES;
  let bp = bodyBase;
  const fmFirst = rawLen > 0 && !hasAnyU;

  // Pass 1: Frontmatter-first skip for drafts/refused when !hasAnyU; unescape body once into SLAB.
  for (let i = 0; i < mdSources.length; i++) {
    const src = mdSources[i];
    const post = src.path.startsWith('posts/');
    let ownReserved = null;
    if (!post) {
      if (src.path.startsWith('tags/')) ownReserved = 'tags';
      else if (src.path.startsWith('page/')) ownReserved = 'page';
    }
    const fileStart = bp;
    let bodyStart = fileStart;
    let fileEnd = fileStart;
    let usedFmFirst = false;

    if (fmFirst) {
      const fmRawEnd = findRawFmEnd(SLAB, rawLat, src.rawS, src.rawE);
      if (fmRawEnd === -2) {
        report.push(`refused ${src.path}: no front matter`);
        continue;
      }
      if (fmRawEnd === -3) {
        report.push(`refused ${src.path}: the front matter is not closed`);
        continue;
      }
      const rawFmLen = fmRawEnd - src.rawS;
      const fmDst = rawFmLen + 16 > FM_BUF.length ? ensureFmBuf(rawFmLen + 16) : FM_BUF;
      const fmLen = unescSmall(SLAB, src.rawS, fmRawEnd, fmDst, UNESC_TBL);
      if (fmLen !== -1) {
        usedFmFirst = true;
        if (!parseFrontMatterBuf(fmDst, FM_BUF_B, 0, fmLen)) {
          report.push(`refused ${src.path}: ${fm.err}`);
          continue;
        }
        if (ownReserved !== null) {
          report.push(`refused ${src.path}: ${ownReserved}/ is the generator's own`);
          continue;
        }
        if (post && fm.date === '') {
          report.push(`refused ${src.path}: a post needs a date`);
          continue;
        }
        const layout = fm.layout !== '' ? fm.layout : (post ? 'post' : 'page');
        if (!rawTpls.has(layout)) {
          report.push(`refused ${src.path}: layout "${layout}" is no template that parses`);
          continue;
        }
        if (fm.draft === true) {
          report.push(`draft ${src.path}`);
          continue;
        }
        const bodyRawS = FM_RAW_BODY_S;
        const bodySpan = src.rawE - bodyRawS;
        if (fileStart + bodySpan + 16 > SLAB.length) ensureSlab(fileStart + bodySpan + 16, fileStart);
        let mdBodyLen = bodySpan > 0 ? K_unescIdxOfCW(SLAB, rawLat, bodyRawS, src.rawE, fileStart, UNESC_TBL) : 0;
        if (mdBodyLen === -1) {
          const bNorm = JSON.parse('"' + SLAB_BUF.toString('utf8', bodyRawS, src.rawE) + '"').replace(/\r\n?/g, '\n');
          const bNeed = Buffer.byteLength(bNorm, 'utf8') + 16;
          if (fileStart + bNeed > SLAB.length) ensureSlab(fileStart + bNeed, fileStart);
          mdBodyLen = SLAB_BUF.utf8Write(bNorm, fileStart);
        }
        bodyStart = fileStart;
        fileEnd = fileStart + mdBodyLen;
      }
    }

    if (!usedFmFirst) {
      let mdLen;
      if (rawLen > 0) {
        const spanLen = src.rawE - src.rawS;
        if (fileStart + spanLen + 16 > SLAB.length) ensureSlab(fileStart + spanLen + 16, fileStart);
        mdLen = K_unescIdxOfCW(SLAB, rawLat, src.rawS, src.rawE, fileStart, UNESC_TBL);
        if (mdLen === -1) {
          const sNorm = JSON.parse(SLAB_BUF.toString('utf8', src.rawS - 1, src.rawE + 1)).replace(/\r\n?/g, '\n');
          const bNeed = Buffer.byteLength(sNorm, 'utf8') + 16;
          if (fileStart + bNeed > SLAB.length) ensureSlab(fileStart + bNeed, fileStart);
          mdLen = SLAB_BUF.utf8Write(sNorm, fileStart);
        }
      } else {
        const sNorm = src.jsContent.indexOf('\r') === -1 ? src.jsContent : src.jsContent.replace(/\r\n?/g, '\n');
        const bNeed = Buffer.byteLength(sNorm, 'utf8') + 16;
        if (fileStart + bNeed > SLAB.length) ensureSlab(fileStart + bNeed, fileStart);
        mdLen = SLAB_BUF.utf8Write(sNorm, fileStart);
      }
      fileEnd = fileStart + mdLen;
      if (!parseFrontMatterBuf(SLAB, SLAB_BUF, fileStart, fileEnd)) {
        report.push(`refused ${src.path}: ${fm.err}`);
        continue;
      }
      if (ownReserved !== null) {
        report.push(`refused ${src.path}: ${ownReserved}/ is the generator's own`);
        continue;
      }
      if (post && fm.date === '') {
        report.push(`refused ${src.path}: a post needs a date`);
        continue;
      }
      const layCheck = fm.layout !== '' ? fm.layout : (post ? 'post' : 'page');
      if (!rawTpls.has(layCheck)) {
        report.push(`refused ${src.path}: layout "${layCheck}" is no template that parses`);
        continue;
      }
      if (fm.draft === true) {
        report.push(`draft ${src.path}`);
        continue;
      }
      bodyStart = fm.bodyStart;
    }

    bp = fileEnd;
    const layout = fm.layout !== '' ? fm.layout : (post ? 'post' : 'page');
    const dir = post ? 'posts' : dirOf(src.path);
    let tSet = takenMap.get(dir);
    if (tSet === undefined) {
      tSet = new Set(dir === '' ? RESERVED : undefined);
      takenMap.set(dir, tSet);
    }
    const slug = uniqueSlug(fm.slug !== '' ? fm.slug : slugifyStr(fm.title, uCache), tSet);
    const outDir = dir === '' ? slug : `${dir}/${slug}`;
    const url = `${base}/${outDir}/`;
    const item = {
      pid: kept.length,
      srcPath: src.path,
      title: fm.title,
      date: fm.date,
      summary: fm.summary,
      tags: fm.tags,
      post,
      layout,
      slug,
      outDir,
      url,
      dateLong: '',
      newerPid: -1,
      olderPid: -1,
      bodyStart,
      bodyEnd: fileEnd,
      tObjs: null,
    };
    kept.push(item);
    bySource.set(src.path, item);
  }

  ensurePageCap(kept.length + 1);
  const staticSet = new Set();
  for (let i = 0; i < statics.length; i++) staticSet.add(statics[i].path);

  const bodyEnd = bp;
  const bodyLat = bodyEnd > bodyBase ? SLAB_BUF.toString('latin1', bodyBase, bodyEnd) : '';
  const hpBox = { hp: bodyEnd };

  // Pre-write every kept page's URL first so writeResolvedHref can copyWithin U8 bytes directly!
  for (let i = 0; i < kept.length; i++) {
    const it = kept[i];
    writeSlotFieldH(it.url, S.pOff, S.pLen, it.pid * PF_STRIDE + 1, hpBox);
  }

  const broken = new Set();
  const dirPartsCache = new Map();
  const linkCtx = { dir: '', upPrefix: [''], dirParts: [], bySource, staticSet, broken, base, srcPath: '', uCache };
  const tocOut = { count: 0 };
  const mdr = MD_RES;

  // Pass 2: Render Markdown directly from SLAB into SLAB, count words & encode page fields!
  for (let i = 0; i < kept.length; i++) {
    const it = kept[i];
    const pid = it.pid;
    const sp = it.srcPath;
    const dir = dirOf(sp);
    let dirMeta = dirPartsCache.get(dir);
    if (dirMeta === undefined) {
      const dirParts = dir === '' ? [] : dir.split('/');
      const upPrefix = new Array(dirParts.length + 1);
      upPrefix[0] = dir === '' ? '' : dir + '/';
      for (let k = 1; k <= dirParts.length; k++) {
        upPrefix[k] = k === dirParts.length ? '' : dirParts.slice(0, dirParts.length - k).join('/') + '/';
      }
      dirMeta = { dirParts, upPrefix };
      dirPartsCache.set(dir, dirMeta);
    }
    linkCtx.dir = dir;
    linkCtx.dirParts = dirMeta.dirParts;
    linkCtx.upPrefix = dirMeta.upPrefix;
    linkCtx.srcPath = sp;

    const bS = it.bodyStart;
    const bE = it.bodyEnd;
    S.pTocStart[pid] = tocOut.count;
    renderMarkdownIntoHBuf(bodyLat, bodyBase, bS, bE, hpBox.hp, linkCtx, tocOut);
    hpBox.hp = mdr.hp;
    S.pTocCount[pid] = tocOut.count - S.pTocStart[pid];

    const words = K_words4(SLAB, bS, bE, W_CLS);
    S.pReadMin[pid] = Math.max(1, Math.ceil(words / 200));
    S.pIsPost[pid] = it.post ? 1 : 0;

    const pBase = pid * PF_STRIDE;
    writeSlotFieldH(it.title, S.pOff, S.pLen, pBase, hpBox);
    writeSlotFieldH(it.date, S.pOff, S.pLen, pBase + 2, hpBox);
    const dl = it.date === '' ? '' : longDate(it.date);
    writeSlotFieldH(dl, S.pOff, S.pLen, pBase + 3, hpBox);
    writeSlotFieldH(it.summary, S.pOff, S.pLen, pBase + 4, hpBox);
    writeSlotFieldH(it.slug, S.pOff, S.pLen, pBase + 5, hpBox);
    S.pOff[pBase + 6] = mdr.excerptOff; S.pLen[pBase + 6] = mdr.excerptLen;
    S.pOff[pBase + 7] = mdr.contentOff; S.pLen[pBase + 7] = mdr.contentLen;
    it.dateLong = dl;
  }

  // Posts sort & newer/older links
  const posts = [];
  for (let i = 0; i < kept.length; i++) if (kept[i].post) posts.push(kept[i]);
  posts.sort((x, y) => byCodeUnits(y.date, x.date) || byCodeUnits(x.slug, y.slug));
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

  // Tags & page tags (using shared OWN_TAG_SEEN to avoid per-page Set allocations)
  const byTagSlug = new Map();
  const allTagsList = [];
  const missingTagMap = new Map();

  for (let i = 0; i < posts.length; i++) {
    const p = posts[i];
    const arr = p.tags;
    if (arr === null || arr.length === 0) { p.tObjs = []; continue; }
    OWN_TAG_SEEN.clear();
    const list = [];
    for (let k = 0; k < arr.length; k++) {
      const name = arr[k];
      const sl = cachedSlug(name, slugCache, uCache);
      if (OWN_TAG_SEEN.has(sl)) continue;
      OWN_TAG_SEEN.add(sl);
      let tObj = byTagSlug.get(sl);
      if (tObj === undefined) {
        tObj = { tid: -1, name, slug: sl, url: `${base}/tags/${sl}/`, posts: [] };
        byTagSlug.set(sl, tObj);
      }
      tObj.posts.push(p);
      list.push(tObj);
    }
    p.tObjs = list;
  }

  const realTags = [...byTagSlug.values()].sort((x, y) => y.posts.length - x.posts.length || byCodeUnits(x.slug, y.slug));
  for (let i = 0; i < realTags.length; i++) {
    realTags[i].tid = allTagsList.length;
    allTagsList.push(realTags[i]);
  }
  for (let i = 0; i < kept.length; i++) {
    const s = kept[i];
    if (s.post) continue;
    const arr = s.tags;
    if (arr === null || arr.length === 0) { s.tObjs = []; continue; }
    OWN_TAG_SEEN.clear();
    const list = [];
    for (let k = 0; k < arr.length; k++) {
      const name = arr[k];
      const sl = cachedSlug(name, slugCache, uCache);
      if (OWN_TAG_SEEN.has(sl)) continue;
      OWN_TAG_SEEN.add(sl);
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
      list.push(tObj);
    }
    s.tObjs = list;
  }

  ensureTagCap(allTagsList.length + 1);
  let tagPostCursor = 0;
  for (let i = 0; i < allTagsList.length; i++) {
    const t = allTagsList[i];
    const tb = i * TF_STRIDE;
    writeSlotFieldH(t.name, S.tOff, S.tLen, tb, hpBox);
    writeSlotFieldH(t.slug, S.tOff, S.tLen, tb + 1, hpBox);
    writeSlotFieldH(t.url, S.tOff, S.tLen, tb + 2, hpBox);
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
    S.pTagCount[pid] = s.tObjs.length;
    ensureAllPageTagsCap(pageTagCursor + s.tObjs.length);
    for (let k = 0; k < s.tObjs.length; k++) S.allPageTags[pageTagCursor++] = s.tObjs[k].tid;
  }

  const tagCardsDyn = new Array(realTags.length);
  for (let i = 0; i < realTags.length; i++) {
    const t = realTags[i];
    tagCardsDyn[i] = { name: t.name, slug: t.slug, url: t.url, count: t.posts.length };
  }
  const recLim = Math.min(inp.site.recent, posts.length);
  const recentDyn = new Array(recLim);
  for (let i = 0; i < recLim; i++) recentDyn[i] = makeDynCard(posts[i], S);
  const siteScope = { vars: { site: siteVar, tags: tagCardsDyn, recent: recentDyn }, parent: null };

  // Pre-compile all needed templates BEFORE reserving pager scratch, card cache, and output region!
  const compiledTpls = new Map();
  const pageTplByLayout = new Map();
  for (let i = 0; i < kept.length; i++) {
    const lay = kept[i].layout;
    if (!pageTplByLayout.has(lay)) {
      pageTplByLayout.set(lay, getCompiledTpl(lay, 'page', rawTpls, compiledTpls, siteScope, hpBox));
    }
  }
  const per = inp.site.per_page;
  const pages = Math.max(1, Math.ceil(posts.length / per));
  const indexComp = getCompiledTpl('index', 'index', rawTpls, compiledTpls, siteScope, hpBox);
  const tagComp = getCompiledTpl('tag', 'tag', rawTpls, compiledTpls, siteScope, hpBox);
  const tagsComp = getCompiledTpl('tags', 'tags', rawTpls, compiledTpls, siteScope, hpBox);

  const pagerBase = hpBox.hp;
  const pagerCap = Math.max(4096, base.length * 18 + 2048);
  const pagerHpBox = { hp: pagerBase };
  const pagerEnd = pagerBase + pagerCap;

  const cardBase = pagerEnd;
  const cardCap = Math.max(512 * 1024, posts.length * 1024);
  S.cp = cardBase;
  S.cardLimit = cardBase + cardCap;

  const outBase = S.cardLimit + (prefixByte !== 0 ? 1 : 0);
  ensureSlab(outBase + 4 * 1024 * 1024, cardBase);
  if (prefixByte !== 0) SLAB[outBase - 1] = prefixByte;
  let op = outBase;

  const writtenKeys = new Set();
  let sep = 123; // '{' on first entry, ',' afterwards

  // Render pages
  for (let i = 0; i < kept.length; i++) {
    const it = kept[i];
    const comp = pageTplByLayout.get(it.layout);
    op = openKv(`${it.outDir}/index.html`, op, writtenKeys, sep); sep = 44;
    if (!comp.needsDynScope) {
      S.regVal[0] = it.pid;
      op = execVm(comp.ops, comp.nWords, op, S);
    } else {
      const sc = { vars: { site: siteVar, tags: tagCardsDyn, recent: recentDyn, page: makeDynPage(it, kept, S) }, parent: null };
      op = writeOutEscJsonStr(renderDynamicPlain(comp.nodes, sc), op);
    }
    op = closeKv(op);
  }

  // Render index pages
  if (indexComp !== null) {
    for (let k = 1; k <= pages; k++) {
      const url = k === 1 ? `${base}/` : `${base}/page/${k}/`;
      const nUrl = k === 1 ? '' : (k === 2 ? `${base}/` : `${base}/page/${k - 1}/`);
      const oUrl = k === pages ? '' : `${base}/page/${k + 1}/`;
      const start = (k - 1) * per;
      const cnt = Math.max(0, Math.min(posts.length, k * per) - start);
      op = openKv(k === 1 ? 'index.html' : `page/${k}/index.html`, op, writtenKeys, sep); sep = 44;
      if (!indexComp.needsDynScope) {
        pagerHpBox.hp = pagerBase;
        writeSlotFieldH(url, S.pgOff, S.pgLen, 0, pagerHpBox);
        writeSlotFieldH(nUrl, S.pgOff, S.pgLen, 1, pagerHpBox);
        writeSlotFieldH(oUrl, S.pgOff, S.pgLen, 2, pagerHpBox);
        S.pgNumber = k; S.pgTotal = pages;
        S.curPostStart = start; S.curPostLen = cnt;
        op = execVm(indexComp.ops, indexComp.nWords, op, S);
      } else {
        const slPosts = posts.slice(start, start + cnt).map((p) => makeDynCard(p, S));
        const pager = { number: k, total: pages, url, newer_url: nUrl, older_url: oUrl };
        const sc = { vars: { site: siteVar, tags: tagCardsDyn, recent: recentDyn, posts: slPosts, pager }, parent: null };
        op = writeOutEscJsonStr(renderDynamicPlain(indexComp.nodes, sc), op);
      }
      op = closeKv(op);
    }
  }

  // Render tag pages
  if (tagComp !== null) {
    for (let i = 0; i < realTags.length; i++) {
      const tp = realTags[i];
      op = openKv(`tags/${tp.slug}/index.html`, op, writtenKeys, sep); sep = 44;
      if (!tagComp.needsDynScope) {
        S.regVal[0] = tp.tid;
        op = execVm(tagComp.ops, tagComp.nWords, op, S);
      } else {
        const tagVar = { name: tp.name, slug: tp.slug, url: tp.url, count: tp.posts.length, posts: tp.posts.map((p) => makeDynCard(p, S)) };
        const sc = { vars: { site: siteVar, tags: tagCardsDyn, recent: recentDyn, tag: tagVar }, parent: null };
        op = writeOutEscJsonStr(renderDynamicPlain(tagComp.nodes, sc), op);
      }
      op = closeKv(op);
    }
  }

  // Render tags index
  if (tagsComp !== null) {
    op = openKv('tags/index.html', op, writtenKeys, sep); sep = 44;
    if (!tagsComp.needsDynScope) {
      op = execVm(tagsComp.ops, tagsComp.nWords, op, S);
    } else {
      op = writeOutEscJsonStr(renderDynamicPlain(tagsComp.nodes, siteScope), op);
    }
    op = closeKv(op);
  }

  // Render static files (ZERO-COPY inside SLAB!)
  for (let i = 0; i < statics.length; i++) {
    const f = statics[i];
    if (writtenKeys.has(f.path)) {
      report.push(`shadowed ${f.path}: a built page has its path`);
      continue;
    }
    if (f.path === 'build-report.txt') continue;
    op = openKv(f.path, op, writtenKeys, sep); sep = 44;
    if (rawLen > 0) {
      const rLen = f.rawE - f.rawS;
      if (op + rLen + 16 > SLAB.length) ensureSlab(op + rLen + 16, op);
      if (rLen > 0) SLAB.copyWithin(op, f.rawS, f.rawE);
      op += rLen;
    } else {
      op = writeOutEscJsonStr(f.jsContent, op);
    }
    op = closeKv(op);
  }

  // Build report
  const rLines = [...report, ...broken].sort(byCodeUnits);
  rLines.push(`built ${kept.length - posts.length} pages, ${posts.length} posts, ${realTags.length} tags and ${statics.length} static files`);
  op = openKv('build-report.txt', op, writtenKeys, sep);
  op = writeOutEscJsonStr(`${rLines.join('\n')}\n`, op);
  op = closeKv(op);

  if (op + 8 > SLAB.length) ensureSlab(op + 8, op);
  SLAB[op++] = 125; // '}'
  if (isLast) SLAB[op++] = 93; // ']'
  outRange.start = prefixByte !== 0 ? outBase - 1 : outBase;
  outRange.end = op;
}

function writeFdAll(fd, buf, start, len) {
  let off = 0;
  while (off < len) off += writeSync(fd, buf, start + off, len - off);
}

const OUT_RANGE = { start: 0, end: 0 };

function runFile(inPath, outPath) {
  const fdIn = openSync(inPath, 'r');
  const rawLen = fstatSync(fdIn).size;
  ensureSlab(rawLen + 6 * 1024 * 1024, 0);
  let rOff = 0;
  while (rOff < rawLen) {
    const n = readSync(fdIn, SLAB, rOff, rawLen - rOff, null);
    if (n <= 0) break;
    rOff += n;
  }
  closeSync(fdIn);
  const rawLat = SLAB_BUF.toString('latin1', 0, rawLen);
  const hasAnyU = rawLat.indexOf('\\u') !== -1;
  const cases = parseCasesRaw(SLAB, SLAB_BUF, rawLat, rawLen);
  const fdOut = openSync(outPath, 'w');
  if (cases.length === 0) {
    SLAB[0] = 91; SLAB[1] = 93;
    writeFdAll(fdOut, SLAB_BUF, 0, 2);
    closeSync(fdOut);
    return;
  }
  for (let i = 0; i < cases.length; i++) {
    buildSiteToOutSlab(cases[i], rawLen, rawLat, hasAnyU, i === 0 ? 91 : 44, i === cases.length - 1, OUT_RANGE);
    cases[i] = null;
    writeFdAll(fdOut, SLAB_BUF, OUT_RANGE.start, OUT_RANGE.end - OUT_RANGE.start);
  }
  closeSync(fdOut);
}

function run(input) {
  const rawFiles = input.files;
  const files = new Array(rawFiles.length);
  for (let i = 0; i < rawFiles.length; i++) {
    const f = rawFiles[i];
    files[i] = { path: f.path, rawS: 0, rawE: 0, isMd: f.path.endsWith('.md'), jsContent: f.content };
  }
  buildSiteToOutSlab({ site: input.site, templates: input.templates, files }, 0, '', false, 0, false, OUT_RANGE);
  return JSON.parse(SLAB_BUF.toString('utf8', OUT_RANGE.start, OUT_RANGE.end));
}

module.exports = { runFile, run };
