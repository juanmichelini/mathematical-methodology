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
  ['results.html', 'CI results'],
  ['appendix-b.html', 'Appendix B'],
  ['developments.html', 'More developments'],
];

const page = (file, title, body, extra = '') => {
  const nav = NAV.map(([f, t]) => `<a href="${f}"${f === file ? ' aria-current="page"' : ''}>${t}</a>`).join('');
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
  return `<details class="lemma ${l.proved ? 'ok' : 'assumed'}" data-q="${esc(search)}">
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
<h1>A method for doing mathematics, written down so that a machine can run it.</h1>
<p class="lead">The thesis describes a method humans can follow with a pen: one that splits the work into what to prove, how to prove it and everything else, and that reduces the rest to patience. This project is that method as a Lean program. The system proposes data types, functions and conjectures, tries to prove them with five tactics, keeps what it proves, and exports every proof as a Lean theorem that Lean itself checks.</p>
<p>${ciBadge}</p>
</section>

<section>
<h2>What the system produced</h2>
<div class="stats">
${stat(json.appendixB.length, 'functions found', 'f0 … f30, the thesis’ Appendix B')}
${stat(counts.appendixB.lemmas, 'lemmas proved about them', `${finished} finished proofs`)}
${stat(counts.suite.proved, 'lemmas in the suite', `the Test.hs lemmas and chains; ${counts.suite.unproved} taken as given`)}
${stat(counts.trees.proved, 'lemmas on a new development', 'polymorphic trees, not in the thesis')}
${stat(`${totalTheorems} / ${totalProved}`, 'Lean theorems / lemmas proved', 'one theorem for every lemma, checked at build')}
</div>
<p>Every lemma on these pages has two forms: the proof the system found, printed the way the thesis prints proofs, and the Lean theorem it was exported to. The generator that writes the Lean file and the one that writes this site use the same numbering, so the pairing is by name and the build fails if a lemma has no theorem or a theorem no lemma. That Lean accepts the theorems is checked by the project’s CI (the “compile gate”), not by this site.</p>
</section>

<section>
<h2>Where to look</h2>
<div class="cards">
<a class="card" href="method.html"><h3>The method</h3><p>The thesis, section by section (the language, the three levels, the five tactics, how the system proposes), each next to the Lean source that implements it.</p></a>
<a class="card" href="results.html"><h3>CI results</h3><p>The report CI regenerates on every change: what the checker accepts and rejects, the searches, the comparison with the original Haskell.</p></a>
<a class="card" href="appendix-b.html"><h3>Appendix B</h3><p>The ${json.appendixB.length} functions and ${counts.appendixB.lemmas} lemmas, each with its proof and its Lean theorem.</p></a>
<a class="card" href="developments.html"><h3>More developments</h3><p>The 35-lemma suite, its lemma chains, and a development the exporter was not written against.</p></a>
</div>
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
<p><a href="appendix-b.html">All ${json.appendixB.length} functions with their proofs →</a></p></div></div></section>`;

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

// ---- CI results (the report)
{
  const toc = rep.sections.filter((s) => s.title).map((s) => `<a href="#${s.id}">${esc(s.title.replace(/`/g, ''))}</a>`).join('');
  write('results.html', page('results.html', 'CI results', `
<div class="layout"><aside class="toc"><b>Report</b>${toc}</aside><div>
<h1>${esc(rep.title)} <small>as CI generates them</small></h1>
<p class="lead">This is <code>results/report.md</code>, rendered. CI regenerates it with <code>lake exe results</code> on a clean machine and fails if it differs from the committed copy, so this page is what the last passing build produced. ${ciBadge}</p>
${rep.sections.map((s) => s.title ? `<section class="rep" id="${s.id}"><h2>${esc(s.title)}</h2>${s.html}</section>` : s.html).join('')}
<p class="muted">The detail behind “Appendix B” and “The lemma suite” is on <a href="appendix-b.html">Appendix B</a> and <a href="developments.html">More developments</a>, with each proof and its Lean theorem.</p>
</div></div>`));
}

const filterBox = `<div class="filter"><input id="q" type="search" placeholder="Filter lemmas (e.g. f3, suma, rev)" autocomplete="off"><button id="expand" type="button">Expand all</button><span id="shown"></span></div>`;

// ---- Appendix B
{
  write('appendix-b.html', page('appendix-b.html', 'Appendix B', `
<h1>Appendix B <small>${json.appendixB.length} functions · ${counts.appendixB.lemmas} lemmas</small></h1>
<p class="lead">The functions the method found by itself, f0 … f30 in the thesis’ numbering, with every lemma it proved about them. Open a lemma to see the proof as the thesis prints proofs and the Lean theorem it was exported to. The counts equal the original Haskell’s (see <a href="results.html#second-search-f3-f30-and-appendix-b">the report</a>).</p>
${filterBox}
${json.appendixB.map((f) => funHtml(f, lean.appendixB, 'appendixb')).join('')}`));
}

// ---- developments
{
  const dev = (name, title, d, leanFiles, blurb) => `
<section class="dev" id="${name}"><h2>${title}</h2><p>${blurb}</p>
${d.functions.map((f) => funHtml({ ...f, lemmas: null }, leanFiles, name)).join('')}
${d.groups.map((g) => `<section class="grp" data-fn="${esc(g.name)}"><h3>${esc(g.name.replace(/^chain_/, 'lemmas found for ').replace(/^lemma$/, 'the 35 lemmas of Test.lemas').replace(/^comp$/, 'lemascomp, the five starting lemmas'))}</h3><div class="lemmas">${g.lemmas.map((l) => lemmaHtml(l, leanFiles, `${name} ${g.name}`)).join('')}</div></section>`).join('')}
</section>`;
  write('developments.html', page('developments.html', 'More developments', `
<h1>More developments <small>${counts.suite.lemmas + counts.trees.lemmas} lemmas</small></h1>
<p class="lead">Two developments beyond Appendix B. The first is the thesis’ own <code>Test</code> module. The second was written to test the export: nothing in the exporter was built for it.</p>
${filterBox}
${dev('suite', 'The lemma suite and the chains of <code>Test.hs</code>', json.suite, lean.suite, `Booleans, naturals and lists; ${counts.suite.proved} lemmas proved of ${counts.suite.lemmas}. Each of the 35 lemmas is proved from the five starting lemmas and the lemmas before it; the chains are the lemmas the method finds for a function, some starting from those of another (<code>flipexp</code> finds the two exponentiation lemmas of thesis §10).`)}
${dev('trees', 'A development the exporter was not written against: polymorphic trees', json.trees, lean.trees, `A new data type (<code>Tree</code>, leaves of any type) with <code>mirror</code>, <code>size</code> and <code>flatten</code>. ${counts.trees.proved} lemmas found, including <code>mirror (mirror t) = t</code>. The inputs are written by hand, as the thesis’ <code>Test</code> is; the lemmas and proofs are found by the system.`)}
`));
}

console.log(`site: built ${fs.readdirSync(OUT).filter((f) => f.endsWith('.html')).length} pages in ${path.relative(ROOT, OUT)}`);
console.log(`site: appendix B ${counts.appendixB.proved}/${counts.appendixB.theorems} lemmas/theorems, suite ${counts.suite.proved}/${counts.suite.theorems} (${counts.suite.unproved} unproved), trees ${counts.trees.proved}/${counts.trees.theorems}`);
