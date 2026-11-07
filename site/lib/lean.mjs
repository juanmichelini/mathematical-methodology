// Reading Lean source: extracting a declaration by name, parsing the generated files, highlighting.
import fs from 'node:fs';
import path from 'node:path';

export const esc = (s) =>
  s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');

const indentOf = (l) => l.match(/^ */)[0].length;
const escRe = (s) => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');

const DECL = '(?:@\\[[^\\]]*\\]\\s*)?(?:(?:partial|private|protected|noncomputable|unsafe)\\s+)*(?:def|theorem|structure|inductive|abbrev|instance|class)';

/**
 * The declaration `symbol` of `file` (path relative to `root`), with the doc comment above it.
 * It ends before the first blank line that is followed by something indented no more than the
 * declaration itself.  Throws if the symbol is not found exactly once: the site must not drift
 * from the code it quotes.
 */
export function extractSymbol(root, file, symbol, opts = {}) {
  const src = fs.readFileSync(path.join(root, file), 'utf8');
  const lines = src.split('\n');
  const re = new RegExp(`^(\\s*)${DECL}\\s+${escRe(symbol)}(?=[\\s:({\\[]|$)`);
  const hits = lines.map((l, i) => (re.test(l) ? i : -1)).filter((i) => i >= 0);
  if (hits.length !== 1) {
    throw new Error(`site: symbol '${symbol}' found ${hits.length} times in ${file} (expected exactly 1)`);
  }
  let start = hits[0];
  const ind = indentOf(lines[start]);
  // doc comment directly above
  let s = start;
  if (s > 0 && lines[s - 1].trim().endsWith('-/')) {
    let j = s - 1;
    while (j >= 0 && !lines[j].includes('/--')) j--;
    if (j >= 0) s = j;
  }
  let end = start;
  for (let i = start + 1; i < lines.length; i++) {
    if (opts.stop && opts.stop.test(lines[i])) break;
    if (lines[i].trim() === '') {
      let k = i + 1;
      while (k < lines.length && lines[k].trim() === '') k++;
      if (k >= lines.length || indentOf(lines[k]) <= ind) break;
    }
    end = i;
  }
  const block = lines.slice(s, end + 1);
  const strip = Math.min(...block.filter((l) => l.trim()).map(indentOf));
  return {
    file,
    symbol,
    code: block.map((l) => l.slice(strip)).join('\n'),
    from: s + 1,
    to: end + 1,
  };
}

/** Blocks of a generated file: `{kind, name, text}` for each top-level `def`/`theorem`/`inductive`. */
export function parseGenerated(root, file) {
  const lines = fs.readFileSync(path.join(root, file), 'utf8').split('\n');
  const starts = [];
  lines.forEach((l, i) => {
    const m = l.match(/^(theorem|def|inductive) (\S+)/);
    if (m) starts.push({ kind: m[1], name: m[2], i });
  });
  const blocks = new Map();
  starts.forEach((b, k) => {
    let end = k + 1 < starts.length ? starts[k + 1].i : lines.length;
    for (let j = b.i; j < end; j++) if (/^end \S+$/.test(lines[j])) { end = j; break; }
    const text = lines.slice(b.i, end).join('\n').replace(/\s+$/, '');
    if (blocks.has(b.name)) throw new Error(`site: ${file}: '${b.name}' defined twice`);
    blocks.set(b.name, { kind: b.kind, name: b.name, text, line: b.i + 1 });
  });
  return blocks;
}

const KEYWORDS = new Set(
  ('def theorem inductive structure abbrev instance class where match with fun let in if then else ' +
    'by at induction generalizing change rw conv lhs rhs rfl try simp exact intro namespace end open ' +
    'mutual deriving termination_by partial private protected import set_option Type Prop Sort ' +
    'have show from calc do return Option Except Nat Bool List String Unit').split(' '),
);

/** Lean source as HTML: comments, strings, numbers and keywords. */
export function highlight(code) {
  const re = /(\/-[\s\S]*?-\/)|(--[^\n]*)|("(?:[^"\\\n]|\\.)*")|\b([A-Za-z_][A-Za-z0-9_']*)\b|(\b\d+\b)/g;
  let out = '';
  let last = 0;
  for (const m of code.matchAll(re)) {
    out += esc(code.slice(last, m.index));
    last = m.index + m[0].length;
    if (m[1] || m[2]) out += `<span class="c">${esc(m[0])}</span>`;
    else if (m[3]) out += `<span class="s">${esc(m[0])}</span>`;
    else if (m[4]) out += KEYWORDS.has(m[4]) ? `<span class="k">${esc(m[0])}</span>` : esc(m[0]);
    else out += `<span class="n">${esc(m[0])}</span>`;
  }
  return out + esc(code.slice(last));
}

export function lineCount(root, file) {
  return fs.readFileSync(path.join(root, file), 'utf8').split('\n').length - 1;
}

export function listLean(root, dir) {
  return fs
    .readdirSync(path.join(root, dir))
    .filter((f) => f.endsWith('.lean'))
    .sort()
    .map((f) => `${dir}/${f}`);
}
