#!/usr/bin/env node
// Builds the website into site/dist from the repository's own artifacts:
//   * the thesis' method        site/content/method.mjs (+ Lean source extracted by symbol name)
//   * the CI report              results/report.md
//   * the results, in detail     results/site-data.json (lake exe site-data) paired with Generated/*.lean
// No dependencies.  Any disagreement between these (a symbol that moved, a lemma without its Lean
// theorem, a Lean theorem without a lemma) fails the build.
import fs from 'node:fs';
import path from 'node:path';
import { execSync } from 'node:child_process';
import { esc, extractSymbol, highlight, lineCount, listLean } from './lib/lean.mjs';
import { renderReport, inline } from './lib/md.mjs';
import { load, lemmasOf, checkDevelopment, checkFunctions, unsanitize, FILES } from './lib/data.mjs';
import { SECTIONS, THESIS } from './content/method.mjs';

const HERE = path.dirname(new URL(import.meta.url).pathname);
const ROOT = path.resolve(HERE, '..');
const OUT = path.join(HERE, 'dist');
const REPO_URL = 'https://github.com/juanmichelini/mathematical-methodology';

const sha =
  process.env.VERCEL_GIT_COMMIT_SHA ||
  (() => { try { return execSync('git rev-parse HEAD', { cwd: ROOT }).toString().trim(); } catch { return ''; } })();

// ---------------------------------------------------------------- data and checks
const { json, report, lean } = load(ROOT);
const counts = {
  appendixB: checkDevelopment('appendixB', json.appendixB, lean.appendixB),
  suite: checkDevelopment('suite', json.suite, lean.suite),
  trees: checkDevelopment('trees', json.trees, lean.trees),
};
checkFunctions('appendixB', json.appendixB, lean.appendixB);
checkFunctions('suite', json.suite.functions, lean.suite);
checkFunctions('trees', json.trees.functions, lean.trees);
if (!/- overall: ok/.test(report)) throw new Error('site: results/report.md does not say "overall: ok"');
// The two sources must agree: the numbers CI prints in the report, and the data the pages are built from.
{
  const rows = [...report.matchAll(/^\| `(f\d+)` \| (\d+) \| (\d+) \|/gm)];
  if (rows.length !== json.appendixB.length) throw new Error(`site: report lists ${rows.length} functions, data has ${json.appendixB.length}`);
  for (const [, name, lemmas, done] of rows) {
    const f = json.appendixB.find((x) => x.name === name);
    const d = f.lemmas.reduce((a, l) => a + l.done, 0);
    if (!f || f.lemmas.length !== +lemmas || d !== +done) {
      throw new Error(`site: ${name}: report says ${lemmas} lemmas / ${done} finished proofs, data has ${f && f.lemmas.length} / ${d}`);
    }
  }
  const said = (re, what, n) => {
    const m = report.match(re);
    if (!m || +m[1] !== n) throw new Error(`site: report ${what}: ${m ? m[1] : 'not found'}, data has ${n}`);
  };
  said(/The (\d+) lemmas found for f0/, 'Appendix B theorems', counts.appendixB.theorems);
  said(/(\d+) theorems are printed;/, 'suite theorems', counts.suite.theorems);
  said(/: (\d+) theorems, lemmas the system/, 'trees theorems', counts.trees.theorems);
}
const rep = renderReport(report);

const totalProved = Object.values(counts).reduce((a, c) => a + c.proved, 0);
const totalTheorems = Object.values(counts).reduce((a, c) => a + c.theorems, 0);
const finished = json.appendixB.flatMap((f) => f.lemmas).reduce((a, l) => a + l.done, 0);
if (totalProved !== totalTheorems) throw new Error('site: proved lemmas and Lean theorems differ');
const cand = (f, re) => [...lean[f].defs.keys()].filter((n) => re.test(n)).length;
const fstCandidates = (() => {
  const src = fs.readFileSync(path.join(ROOT, 'MathematicalMethodology/Generated/FstCandidates.lean'), 'utf8');
  return (src.match(/^def fstCand\d+/gm) || []).length;
})();

// ---------------------------------------------------------------- HTML helpers
const NAV = [
  ['index.html', 'Overview'],
  ['method.html', 'The method'],
  ['verification.html', 'Verification'],
  ['results.html', 'Results'],
];
// pages under Results keep that tab highlighted
const tabOf = (file) => (file.startsWith('results-') ? 'results.html' : file);

const page = (file, title, body, extra = '') => {
  const nav = NAV.map(([f, t]) => `<a href="${f}"${f === tabOf(file) ? ' aria-current="page"' : ''}>${t}</a>`).join('');
  return `<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>${esc(title)} · Mathematical Methodology in Lean</title>
<meta name="description" content="The method of the thesis ‘Foundations for Mathematical Methodology’, beside its Lean implementation and the results CI produces.">
<link rel="stylesheet" href="assets/style.css">
</head>
<body>
<header class="top"><div class="wrap">
<a class="brand" href="index.html"><span class="mark">∀</span> Mathematical Methodology <em>in Lean</em></a>
<nav>${nav}</nav>
</div></header>
<main class="wrap">
${body}
</main>
<footer class="wrap foot">
<p>Generated from the repository by <code>site/build.mjs</code>${sha ? ` at <a href="${REPO_URL}/commit/${sha}"><code>${sha.slice(0, 7)}</code></a>` : ''}. Nothing on these pages is typed by hand except the thesis text and the commentary: definitions, numbers, proofs and Lean code are read from the code and from CI’s outputs, and the build fails if they disagree.</p>
</footer>
<script src="assets/app.js"></script>
${extra}
</body>
</html>
`;
};

const ghLink = (file, from, to) => `${REPO_URL}/blob/main/${file}#L${from}-L${to}`;

const codeBlock = (code, { caption, file, from, to, lang = 'lean' } = {}) => `
<figure class="code">
${caption ? `<figcaption><span>${esc(caption)}</span>${file ? `<a href="${ghLink(file, from, to)}"><code>${esc(file.replace('MathematicalMethodology/', ''))}:${from}</code></a>` : ''}</figcaption>` : ''}
<pre class="${lang}"><code>${lang === 'lean' ? highlight(code) : esc(code)}</code></pre>
</figure>`;

const statementHtml = (st) => {
  const [vars, eq] = st.split(' |- ');
  const vs = vars.trim() ? vars.trim().split(' ').map((v) => v.replace(':', ' : ')).join(', ') : '';
  return `<span class="stmt">${vs ? `<span class="q">∀ ${esc(vs)}.</span> ` : ''}<span class="eq">${esc(eq)}</span></span>`;
};

const proofHtml = (lines) => {
  let out = '<div class="proof">';
  let prevCase = false;
  for (const l of lines) {
    const pad = `style="--d:${l.d}"`;
    if (l.k === 'case') { out += `<div class="pl case" ${pad}>${esc(l.t)}</div>`; prevCase = true; continue; }
    if (l.k === 'hyp') { out += `<div class="pl hyp" ${pad}><b>H)</b> ${esc(l.t)}</div>`; continue; }
    if (l.k === 'goal') { out += `<div class="pl goal" ${pad}>${prevCase ? '<b>T)</b> ' : ''}${esc(l.t)}</div>`; prevCase = false; continue; }
    if (l.k === 'step') { out += `<div class="pl step" ${pad}>{ ${esc(l.t)} }</div>`; continue; }
    out += `<div class="pl ${l.k}" ${pad}>${esc(l.t)}</div>`;
  }
  return out + '</div>';
};

const lemmaHtml = (l, leanFiles, tag) => {
  const thm = l.id ? leanFiles.thms.get(l.id) : null;
  const search = `${tag} ${l.statement} ${l.id || ''}`.toLowerCase();
  return `<details class="lemma ${l.proved ? 'ok' : 'assumed'}"${l.id ? ` id="lemma-${esc(l.id)}"` : ''} data-q="${esc(search)}">
<summary>${statementHtml(l.statement)}${
    l.proved
      ? `<span class="badge lean" title="the Lean theorem this lemma was exported to">${esc(l.id)}</span><span class="badge n" title="finished proofs">${l.done}</span>`
      : '<span class="badge warn" title="not proved by the system; the Haskell takes it as given">assumed</span>'
  }</summary>
${
    l.proved
      ? `<div class="cols"><div><h4>The system’s proof <small>thesis format</small></h4>${proofHtml(l.proof)}</div>
<div><h4>The same, as a Lean theorem <small>checked by Lean in CI</small></h4>${codeBlock(thm.text, { })}</div></div>`
      : '<p class="muted">The system did not prove this one; it is a starting hypothesis of the suite (a <code>lemascomp</code> lemma). It needs commutativity of <code>suma</code>, which the suite proves later.</p>'
  }
</details>`;
};

const funHtml = (f, leanFiles, tag) => `
<section class="fn" id="${esc(f.name)}" data-fn="${esc(f.name)}">
<h3><code>${esc(f.name)}</code> <span class="type">${esc(f.type)}</span></h3>
<div class="cols">
<div><h4>Definition <small>thesis notation</small></h4><pre class="plain"><code>${esc(f.definition)}</code></pre></div>
<div><h4>Exported to Lean</h4>${codeBlock(leanFiles.defs.get(f.name).text, {})}</div>
</div>
${f.lemmas ? `<h4>${f.lemmas.length} lemma${f.lemmas.length === 1 ? '' : 's'}</h4><div class="lemmas">${f.lemmas.map((l) => lemmaHtml(l, leanFiles, `${tag} ${f.name}`)).join('')}</div>` : ''}
</section>`;

// ---------------------------------------------------------------- CI status (optional)
async function ciStatus() {
  const token = process.env.GITHUB_TOKEN;
  if (!sha || !token || process.env.SITE_OFFLINE) return null;
  try {
    const r = await fetch(`https://api.github.com/repos/juanmichelini/mathematical-methodology/commits/${sha}/check-runs`, {
      headers: { authorization: `Bearer ${token}`, accept: 'application/vnd.github+json' },
      signal: AbortSignal.timeout(8000),
    });
    if (!r.ok) return null;
    const j = await r.json();
    if (!j.check_runs?.length) return { state: 'none' };
    if (j.check_runs.some((c) => c.status !== 'completed')) return { state: 'running' };
    return { state: j.check_runs.every((c) => c.conclusion === 'success') ? 'success' : 'failure' };
  } catch { return null; }
}
const ci = await ciStatus();
const ciBadge = ci
  ? `<span class="ci ${ci.state}">CI at this commit: ${({ success: 'passing', failure: 'failing', running: 'still running when this was built', none: 'no runs' })[ci.state]}</span>`
  : '<span class="ci unknown">CI status is not read at build time (set <code>GITHUB_TOKEN</code> to show it)</span>';

// ---------------------------------------------------------------- pages
fs.rmSync(OUT, { recursive: true, force: true });
fs.mkdirSync(path.join(OUT, 'assets'), { recursive: true });
for (const f of ['style.css', 'app.js']) fs.copyFileSync(path.join(HERE, 'assets', f), path.join(OUT, 'assets', f));
const write = (f, html) => fs.writeFileSync(path.join(OUT, f), html);

// ---- overview
{
  const stat = (n, label, sub) => `<div class="stat"><b>${n}</b><span>${label}</span>${sub ? `<small>${sub}</small>` : ''}</div>`;
  write('index.html', page('index.html', 'Overview', `
<section class="hero">
<p class="kicker">${esc(THESIS.title)} · ${esc(THESIS.author)}, ${esc(THESIS.school)}, ${THESIS.year}</p>
<h1>A method for doing mathematics, written down so that humans can follow it and a machine can run it.</h1>
<p class="lead">The thesis describes a method humans can follow with a pen: one that splits the work into what to prove, how to prove it and everything else, and that reduces the rest to patience. This project is that method as a Lean program. The system proposes data types, functions and conjectures, tries to prove them with five tactics, keeps what it proves, and exports every proof as a Lean theorem that Lean itself checks.</p>
<p>${ciBadge}</p>
</section>

<section>
<h2>The three parts</h2>
<div class="cards">
<a class="card" href="method.html"><h3>1. The method</h3><p>What the thesis says, section by section (the language, the three levels, the five tactics, how the system proposes what to prove), each next to the Lean code that implements it.</p></a>
<a class="card" href="verification.html"><h3>2. Verification</h3><p>How we know the Lean version is right: the checker rejects wrong proofs, the searches reproduce what the original Haskell program did, and Lean accepts every proof the system finds. The report CI regenerates on every change.</p></a>
<a class="card" href="results.html"><h3>3. Results</h3><p>What the method found: the ${json.appendixB.length} functions of the thesis’ Appendix B, the thesis’ <code>Test</code> lemmas, and a new development, each lemma with its proof and its Lean theorem.</p></a>
</div>
</section>

<section>
<h2>In numbers</h2>
<div class="stats">
${stat(json.appendixB.length, 'functions found', 'f0 … f30, the thesis’ Appendix B')}
${stat(counts.appendixB.lemmas, 'lemmas proved about them', `${finished} finished proofs`)}
${stat(counts.suite.proved, 'lemmas in the thesis’ Test module', `${counts.suite.unproved} taken as given, not proved`)}
${stat(counts.trees.proved, 'lemmas on a new development', 'polymorphic trees, not in the thesis')}
${stat(`${totalTheorems} / ${totalProved}`, 'Lean theorems / lemmas proved', 'one theorem for every lemma, checked at build')}
</div>
<p>Every lemma has two forms: the proof the system found, printed the way the thesis prints proofs, and the Lean theorem it was exported to. The generator that writes the Lean files and the one that writes this site number them the same way, so the pairing is by name and the build fails if a lemma has no theorem or a theorem no lemma. That Lean accepts the theorems is checked by the project’s CI (the “compile gate”), not by this site.</p>
</section>`));
}

// ---- method
{
  const levelRows = [
    ['Strategic', 'what to prove', 'MathematicalMethodology/Strategic', 'proposes; untrusted'],
    ['Tactical', 'how to prove it', 'MathematicalMethodology/Tactical', 'search is untrusted; only the checker (Cert.check) is trusted'],
    ['Operational', 'what is possible', 'MathematicalMethodology/Operational', 'trusted, small'],
  ].map(([n, q, dir, trust]) => {
    const files = listLean(ROOT, dir);
    const lines = files.reduce((a, f) => a + lineCount(ROOT, f), 0);
    return `<tr><td><b>${n}</b></td><td>${q}</td><td><code>${dir.replace('MathematicalMethodology/', '')}/</code></td><td>${files.length} files, ${lines} lines</td><td>${trust}</td></tr>`;
  }).join('');

  const sectionHtml = (s) => {
    const parts = [];
    parts.push(`<div class="thesis"><h4>The thesis <small>§${esc(s.num)} · abridged, [...] marks omissions</small></h4>${s.thesis.map((p) => `<blockquote>${esc(p)}</blockquote>`).join('')}${s.code ? codeBlock(s.code, { caption: s.codeCaption, lang: 'plain' }) : ''}</div>`);
    let right = `<div class="inlean"><h4>In Lean</h4>${s.note ? `<p class="note">${esc(s.note)}</p>` : ''}`;
    if (s.levels) right += `<div class="tablewrap"><table><thead><tr><th>level</th><th>question</th><th>code</th><th>size</th><th>trust</th></tr></thead><tbody>${levelRows}</tbody></table></div>`;
    for (const r of s.lean || []) {
      const x = extractSymbol(ROOT, r.file, r.symbol, { stop: r.stop });
      right += codeBlock(x.code, { caption: r.caption, file: x.file, from: x.from, to: x.to });
    }
    if (s.snippet) {
      const src = fs.readFileSync(path.join(ROOT, s.snippet.file), 'utf8').split('\n');
      const i = src.findIndex((l) => s.snippet.after.test(l));
      if (i < 0) throw new Error(`site: snippet not found in ${s.snippet.file}: ${s.snippet.after}`);
      const block = src.slice(i, i + s.snippet.count + 1);
      const strip = Math.min(...block.filter((l) => l.trim()).map((l) => l.match(/^ */)[0].length));
      right += codeBlock(block.map((l) => l.slice(strip)).join('\n'), { caption: s.snippet.caption, file: s.snippet.file, from: i + 1, to: i + block.length });
    }
    if (s.modules) {
      right += `<div class="tablewrap"><table><thead><tr><th>thesis (Haskell)</th><th>Lean</th></tr></thead><tbody>${s.modules.map((m) => `<tr><td>${esc(m.thesis)}</td><td>${m.lean.map((f) => {
        if (!fs.existsSync(path.join(ROOT, f))) throw new Error(`site: missing file ${f}`);
        return `<a href="${REPO_URL}/blob/main/${f}"><code>${esc(f.replace('MathematicalMethodology/', ''))}</code></a> <small>${lineCount(ROOT, f)} lines</small>`;
      }).join('<br>')}</td></tr>`).join('')}</tbody></table></div>`;
    }
    if (s.dataTypes) {
      const inds = [...lean.appendixB.defs.values()].filter((b) => b.kind === 'inductive').slice(0, 6);
      right += `<p class="note">The data types the first search used (${fstCandidates} candidate functions over them), canonical name and Lean:</p><div class="tablewrap"><table><thead><tr><th>canonical name</th><th>Lean</th></tr></thead><tbody>${inds.map((b) => `<tr><td><code>${esc(unsanitize(b.name))}</code></td><td><pre class="lean inline"><code>${highlight(b.text)}</code></pre></td></tr>`).join('')}</tbody></table></div>`;
    }
    if (s.id === 'functions') right += `<p class="note">${fstCandidates} functions in the first search; the report below counts the second search’s 164 candidates.</p>`;
    right += '</div>';
    parts.push(right);
    let extra = '';
    if (s.exampleProof) {
      const f = json.appendixB.find((x) => x.name === s.exampleProof.fn);
      const l = f.lemmas.find((x) => x.statement === s.exampleProof.statement);
      if (!l) throw new Error(`site: example lemma not found: ${s.exampleProof.fn} ${s.exampleProof.statement}`);
      extra = `<div class="example"><h4>${esc(s.exampleProof.title)}: ${statementHtml(l.statement)}</h4><div class="cols"><div><h5>The system’s proof <small>thesis format</small></h5>${proofHtml(l.proof)}</div><div><h5>As a Lean theorem <small>${esc(l.id)}</small></h5>${codeBlock(lean.appendixB.thms.get(l.id).text, {})}</div></div></div>`;
    }
    return `<section class="msec" id="${s.id}"><h2><span class="num">§${esc(s.num)}</span> ${esc(s.title)}</h2><div class="cols wide">${parts.join('')}</div>${extra}</section>`;
  };

  const resultsSection = `<section class="msec" id="results"><h2><span class="num">§10</span> Results</h2>
<div class="cols wide"><div class="thesis"><h4>The thesis <small>§10 · abridged</small></h4>
<blockquote>On its first pass, it discovered the addition (f0 in appendix B) and the concatenation (f2). It also discovered a variant of addition (f1), that is the function (λ x y . x+y +1). [...] We then ran the method again, this time searching for functions that used addition and concatenation as auxiliary functions. It found reverse f3 and the fact that it is its own inverse. [...] The method found multiplication (f12) and many variants of it.</blockquote></div>
<div class="inlean"><h4>In Lean</h4><p class="note">The same runs, read from this build’s data.</p>
${['f0', 'f1', 'f2', 'f3', 'f12'].map((n) => { const f = json.appendixB.find((x) => x.name === n); return `<p><code>${n}</code> = <code>${esc(f.definition)}</code> <small>${f.lemmas.length} lemmas</small></p>`; }).join('')}
<p><a href="results-appendix-b.html">All ${json.appendixB.length} functions with their proofs →</a></p></div></div></section>`;

  const toc = [...SECTIONS, { id: 'results', num: '10', title: 'Results' }]
    .map((s) => `<a href="#${s.id}"><span>§${esc(s.num)}</span> ${esc(s.title)}</a>`).join('');
  write('method.html', page('method.html', 'The method', `
<div class="layout"><aside class="toc"><b>Contents</b>${toc}</aside><div>
<h1>The method, as in the thesis, and in Lean</h1>
<p class="lead">Each section follows the thesis. On the left is what the thesis says; on the right, the Lean code that does it, read from the repository when this site is built (click the file name to open it).</p>
${SECTIONS.map(sectionHtml).join('')}
${resultsSection}
</div></div>`));
}

// ---- Verification (the CI report, grouped by the question it answers)
const GROUPS = [
  ['Does the checker reject what is wrong?', 'The only trusted piece is the proof checker. These sections show it accepts correct certificates, rejects wrong ones, and that its soundness is a Lean theorem.',
    ['development-lists', 'negative-tests', 'soundness']],
  ['Does the search do what the original program did?', 'The searches are untrusted ports of the thesis’ Haskell program. Each stage is compared with output printed by the original: enumeration in order, conjectures, the lemmas found, and the 31 functions of Appendix B.',
    ['summary', 'lemma-store', 'tactic-search', 'enumeration', 'conjectures', 'finding-lemmas', 'first-search-f0-f2', 'second-search-f3-f30-and-appendix-b', 'the-lemma-suite-of-test-hs']],
  ['Does Lean accept what the system found?', 'Every proof the system finds is printed as a Lean theorem and Lean checks it. A proof that does not compile is a reported failure, not a silent gap.',
    ['export-to-lean']],
];
{
  const have = rep.sections.filter((x) => x.title).map((x) => x.id);
  const assigned = GROUPS.flatMap((g) => g[2]);
  for (const id of have) if (!assigned.includes(id)) throw new Error(`site: report section "${id}" is not assigned to a Verification group`);
  for (const id of assigned) if (!have.includes(id)) throw new Error(`site: Verification group names a report section that does not exist: ${id}`);
  const byId = new Map(rep.sections.filter((x) => x.title).map((x) => [x.id, x]));
  const toc = GROUPS.map(([t, , ids]) => `<b class="tocgrp">${esc(t)}</b>` + ids.map((id) => `<a href="#${id}">${esc(byId.get(id).title.replace(/`/g, ''))}</a>`).join('')).join('');
  const pairRows = [['Appendix B', counts.appendixB], ['The Test suite', counts.suite], ['Trees', counts.trees]]
    .map(([n, c]) => `<tr><td>${n}</td><td>${c.lemmas}</td><td>${c.proved}</td><td>${c.theorems}</td></tr>`).join('');
  write('verification.html', page('verification.html', 'Verification', `
<div class="layout"><aside class="toc"><b>Verification</b>${toc}</aside><div>
<h1>Verification <small>as CI generates it</small></h1>
<p class="lead">How we know the Lean version is right. This is <code>results/report.md</code>, rendered: CI regenerates it with <code>lake exe results</code> on a clean machine and fails if it differs from the committed copy. The sections are grouped by the question each one answers.</p>
<p>${ciBadge}</p>
<section class="rep"><h2>Lemmas and Lean theorems</h2>
<p>Each lemma the system proves is exported as one Lean theorem. This site is built from both and fails if they do not pair up by name.</p>
<div class="tablewrap"><table><thead><tr><th>development</th><th>lemmas</th><th>proved</th><th>Lean theorems</th></tr></thead><tbody>${pairRows}</tbody></table></div>
<p class="muted">Lean accepting the theorems is checked by CI (the compile gate and axiom check), not by this site.</p></section>
${GROUPS.map(([t, d, ids]) => `<div class="vgroup"><h2 class="vq">${esc(t)}</h2><p class="lead">${esc(d)}</p>${ids.map((id) => { const x = byId.get(id); return `<section class="rep" id="${x.id}"><h3>${esc(x.title)}</h3>${x.html}</section>`; }).join('')}</div>`).join('')}
</div></div>`));
}

const filterBox = `<div class="filter"><input id="q" type="search" placeholder="Filter lemmas (e.g. f3, suma, rev)" autocomplete="off"><button id="expand" type="button">Expand all</button><span id="shown"></span></div>`;

// ---- Results
const dev = (name, title, d, leanFiles, blurb) => `
<section class="dev" id="${name}"><p>${blurb}</p>
${d.functions.map((f) => funHtml({ ...f, lemmas: null }, leanFiles, name)).join('')}
${d.groups.map((g) => `<section class="grp" data-fn="${esc(g.name)}"><h3>${esc(g.name.replace(/^chain_/, 'lemmas found for ').replace(/^lemma$/, 'the 35 lemmas of Test.lemas').replace(/^comp$/, 'lemascomp, the five starting lemmas'))}</h3><div class="lemmas">${g.lemmas.map((l) => lemmaHtml(l, leanFiles, `${name} ${g.name}`)).join('')}</div></section>`).join('')}
</section>`;
{
  const fn = (n) => { const f = json.appendixB.find((x) => x.name === n); if (!f) throw new Error(`site: no ${n} in Appendix B`); return f; };
  const lem = (n, st) => { const l = fn(n).lemmas.find((x) => x.statement === st); if (!l) throw new Error(`site: ${n} has no lemma "${st}"`); return l; };
  const rev = lem('f3', 'a:C_,a_R |- f3 (f3 a) = a');
  const claims = [
    ['Addition is discovered first (f0)', 'f0', fn('f0'), 'f0 is defined by recursion on its first argument and has commutativity and associativity among its lemmas.', lem('f0', 'c:C_,R d:C_,R |- f0 c d = f0 d c')],
    ['A variant of addition, x+y+1 (f1)', 'f1', fn('f1'), 'Same shape as f0 with a successor in the base case.', lem('f1', 'c:C_,R d:C_,R |- f1 c d = f1 d c')],
    ['Concatenation (f2)', 'f2', fn('f2'), 'Recursion on a list; has the two units and associativity.', lem('f2', 'b:C_,a_R e:C_,a_R g:C_,a_R |- f2 b (f2 e g) = f2 (f2 b e) g')],
    ['Reverse (f3), and that it is its own inverse', 'f3', fn('f3'), 'Found in the second search, using f2 as an auxiliary function.', rev],
  ];
  const claimRows = claims.map(([c, n, f, note, l]) => `<tr><td>${c}</td><td><code>${n}</code> = <code>${esc(f.definition)}</code></td><td>${statementHtml(l.statement)} <small>(${l.done ? 'proof finished' : 'assumed'})</small></td><td><a href="results-appendix-b.html#lemma-${esc(l.id)}">proof</a></td></tr>`).join('');
  const card = (href, h, n, text) => `<a class="card" href="${href}"><h3>${h}</h3><p><b>${n}</b> · ${text}</p></a>`;
  write('results.html', page('results.html', 'Results', `
<h1>Results</h1>
<p class="lead">What the method found. Every lemma on these pages has the proof the system found, printed the way the thesis prints proofs, and the Lean theorem it was exported to.</p>
<div class="cards">
${card('results-appendix-b.html', 'Appendix B', `${json.appendixB.length} functions, ${counts.appendixB.lemmas} lemmas`, 'The functions the system found by itself, f0 … f30, with every lemma about them. This is what the thesis reports.')}
${card('results-suite.html', 'The Test suite', `${counts.suite.proved} lemmas`, 'The thesis’ own <code>Test</code> module: Booleans, naturals and lists. The 35 lemmas and the chains of lemmas, proved in order.')}
${card('results-trees.html', 'A new development', `${counts.trees.proved} lemmas`, 'Polymorphic trees. Not in the thesis, written to test the pipeline: nothing in the exporter was built for it.')}
</div>
<section><h2>What the thesis says, and what this run produced</h2>
<p>The thesis’ §10 reports a handful of discoveries. Each row is looked up in the data this site is built from; the build fails if one is missing.</p>
<div class="tablewrap"><table><thead><tr><th>thesis</th><th>found</th><th>lemma</th><th></th></tr></thead><tbody>${claimRows}</tbody></table></div></section>`));

  const sub = (file, title, small, lead, body) => write(file, page(file, title, `
<p class="crumbs"><a href="results.html">Results</a> › ${esc(title)}</p>
<h1>${esc(title)} <small>${small}</small></h1>
<p class="lead">${lead}</p>
${filterBox}
${body}`));
  sub('results-appendix-b.html', 'Appendix B', `${json.appendixB.length} functions · ${counts.appendixB.lemmas} lemmas`,
    'The functions the method found by itself, f0 … f30 in the thesis’ numbering, with every lemma it proved about them. Open a lemma to see the proof as the thesis prints proofs and the Lean theorem.',
    json.appendixB.map((f) => funHtml(f, lean.appendixB, 'appendixb')).join(''));
  sub('results-suite.html', 'The Test suite', `${counts.suite.lemmas} lemmas`,
    'The thesis’ own <code>Test</code> module, proved by the system.',
    dev('suite', '', json.suite, lean.suite, `Booleans, naturals and lists; ${counts.suite.proved} lemmas proved of ${counts.suite.lemmas}. ${counts.suite.unproved} lemma(s) taken as given, as the original program does.`));
  sub('results-trees.html', 'A new development', `${counts.trees.lemmas} lemmas`,
    'Polymorphic trees. Written to test the export on something the exporter was not built for.',
    dev('trees', '', json.trees, lean.trees, 'A new data type (<code>Tree</code>, leaves of any type) with <code>mirror</code>, <code>size</code> and <code>flatten</code>, proved the same way.'));
}

console.log(`site: built ${fs.readdirSync(OUT).filter((f) => f.endsWith('.html')).length} pages in ${path.relative(ROOT, OUT)}`);
console.log(`site: appendix B ${counts.appendixB.proved}/${counts.appendixB.theorems} lemmas/theorems, suite ${counts.suite.proved}/${counts.suite.theorems} (${counts.suite.unproved} unproved), trees ${counts.trees.proved}/${counts.trees.theorems}`);
