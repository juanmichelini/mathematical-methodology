// Loading the repository's artifacts and checking that they agree with each other.
import fs from 'node:fs';
import path from 'node:path';
import { parseGenerated } from './lean.mjs';

export const FILES = {
  appendixB: { defs: 'MathematicalMethodology/Generated/AppendixB.lean', thms: 'MathematicalMethodology/Generated/AppendixBProofs.lean' },
  suite: { defs: 'MathematicalMethodology/Generated/Suite.lean', thms: 'MathematicalMethodology/Generated/Suite.lean' },
  trees: { defs: 'MathematicalMethodology/Generated/Trees.lean', thms: 'MathematicalMethodology/Generated/Trees.lean' },
};

/** Lean identifier -> the prototype's canonical name (inverse of the exporter's `sanitize`). */
export const unsanitize = (s) => s.replace(/_u/g, '_').replace(/_c/g, ',').replace(/_d/g, '.');

export function load(root) {
  const json = JSON.parse(fs.readFileSync(path.join(root, 'results/site-data.json'), 'utf8'));
  const report = fs.readFileSync(path.join(root, 'results/report.md'), 'utf8');
  const lean = {};
  for (const [k, f] of Object.entries(FILES)) {
    lean[k] = { defs: parseGenerated(root, f.defs), thms: parseGenerated(root, f.thms) };
  }
  return { json, report, lean };
}

/** Lemmas of a development as a flat list, in order, with their group/function. */
export function lemmasOf(dev) {
  if (Array.isArray(dev)) return dev.flatMap((f) => f.lemmas.map((l) => ({ ...l, group: f.name })));
  return dev.groups.flatMap((g) => g.lemmas.map((l) => ({ ...l, group: g.name })));
}

/**
 * The correspondence the site is built on: every lemma the system proved has exactly one Lean
 * theorem, and every Lean theorem of the generated file is the export of exactly one lemma.
 * Returns the counts; throws if the two sides disagree.
 */
export function checkDevelopment(name, dev, leanFiles) {
  const lemmas = lemmasOf(dev);
  const proved = lemmas.filter((l) => l.proved);
  const thms = [...leanFiles.thms.values()].filter((b) => b.kind === 'theorem');
  const ids = new Set();
  for (const l of proved) {
    if (!l.id) throw new Error(`site: ${name}: a proved lemma has no theorem name: ${l.statement}`);
    if (ids.has(l.id)) throw new Error(`site: ${name}: theorem name used twice: ${l.id}`);
    ids.add(l.id);
    if (!leanFiles.thms.has(l.id)) throw new Error(`site: ${name}: no Lean theorem '${l.id}' for ${l.statement}`);
  }
  for (const t of thms) {
    if (!ids.has(t.name)) throw new Error(`site: ${name}: Lean theorem '${t.name}' belongs to no lemma`);
  }
  for (const l of lemmas) {
    if (!l.proved && l.id) throw new Error(`site: ${name}: unproved lemma with a theorem name`);
  }
  return { lemmas: lemmas.length, proved: proved.length, theorems: thms.length, unproved: lemmas.length - proved.length };
}

export function checkFunctions(name, funs, leanFiles) {
  for (const f of funs) {
    if (!leanFiles.defs.has(f.name)) throw new Error(`site: ${name}: no Lean definition '${f.name}'`);
  }
}
