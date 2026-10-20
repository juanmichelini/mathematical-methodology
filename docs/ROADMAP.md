# Roadmap

Each item below should become an issue before work starts (see `AGENTS.md`).

## Done (v0)

- Operational level: de Bruijn terms, substitution, beta/case/delta, `computeSafe`/`computeWide`.
- Tactical level: `Affirm`, `Rule`, `Cert`, `Cert.check`, `checkDevelopment`.
- Example: `append_nil`, `append_assoc`, `rev_append`, `rev_rev` as checked certificates.
- Deterministic results report (`lake exe results`), committed in `results/` and verified by CI.
- **Soundness of `Cert.check`** (`Semantics/`): `Cert.check_sound`, `checkDevelopment_valid`,
  conditional on `EnvClosed`, `SigSound`, `DataWF`; discharged for the list example in
  `Examples/ListsSound.lean`. The checker gained first-order types for lemma instances
  (`Ctx.typeOf`), a scope check for induction, and dropped rigid rules on nested induction.

- Parity with foundations (issues #18, #22-#29): lemma store and ordering (`Tactical/Store.lean`,
  port of `Rec`, `fund`, `dependencies`, `addAffirm` from `Prove.hs`; #24) and the tactic
  search (`Tactical/Search.lean`, port of `mainTactic`; #18): it rediscovers the four list
  lemmas, which `Cert.check` accepts. Enumeration of data types and functions
  (`Strategic/Enumerate.lean`, `enum*` of `Propose.hs`; #22): `datas` and the 64 first-search
  candidates match foundations. The 164 second-search candidates depend on the first
  search's output (`fstEnv`) and are checked with #26/#27. The strategic level works
  directly on de Bruijn `Term` (#33, no named syntax); the 64 candidates are identical, in
  order, to what the original Haskell prints (`Examples/HaskellFst.lean`).

- Export to Lean (#34): data types as `inductive`, generated functions as `def` + `match`;
  the 64 first-search candidates compile in real Lean and `suma` and list `append` run
  (`Export/Lean.lean`, `Generated/FstCandidates.lean`, `Examples/ExportCheck.lean`).

- Conjecture generation (#23): `Strategic/Conjecture.lean`. For the 64 first-search candidates
  (8222 lines) and for the functions of `Test.hs` (89215 lines, `ampleAll`/`conjeturasAll`
  included) the Lean conjectures are identical to the Haskell's, names and order included.
  Not ported, as no search calls them: `conjeturasFloatsDep`, `enumAppStarting*`,
  `armarUsarTodo*`, `joinVar`, `permutVars`, `instanceAll`, `toPTT`.

- `findlemas`/`provell` and the `paciencia` limit (#25): `Tactical/Prove.lean`,
  `Strategic/FindLemmas.lean`. On the 64 first-search candidates the whole `provell` trace
  (conjectures tried, proofs completed, smallest budget for each, lemma chosen) is identical
  to the Haskell's, and the `paciencia` table of foundations is reproduced (0 / 4,4,4 /
  7,7,4). All 18 lemmas found are also certified by `Cert.check` via `Tactical/Search.lean`.

- First search (#26): `Strategic/FirstSearch.lean`. 64 candidates, 3 kept (f0 = addition,
  f1 = addition with a successor base, f2 = list append), 7+7+4 lemmas, 17+17+6 finished
  proofs as in Appendix B; the definitions (with Haskell's refreshed binder names), the lemma
  statements and the whole store `fstRec` are identical to the Haskell's.

- Second search and Appendix B (#27): `Strategic/SecondSearch.lean`. 164 candidates (41 unary,
  123 binary), 28 kept (f3..f30; f3 is `reverse`, with `f3 (f2 a b) = f2 (f3 b) (f3 a)` and
  `f3 (f3 a) = a`). All 31 functions match Appendix B's lemma and finished-proof counts, and
  the candidates, definitions (with Haskell's binder names), lemma statements and counts are
  identical to the original Haskell's output. `lake exe results` runs it (about a minute).

- The lemma suite and `flipexp` (#28): `Examples/TestSuite.lean`. All 35 lemmas of `Test.lemas`
  are proved (each at the same smallest budget as in the Haskell), and the chains of `Test.hs`
  (suma, mult, flipexp, min, max, absr, and, or, not, concat, rev) find the same lemmas and
  finished-proof counts, including the two exponentiation lemmas of thesis Sec. 10.

- Export of the 31 functions of Appendix B (#47): `Generated/AppendixB.lean`; Lean accepts all of
  them, and addition, append and `reverse` (f3) run.

- Proofs as Lean theorems (#35; not yet parity plus, see #53): `Export/Proofs.lean`, `Generated/AppendixBProofs.lean`:
  the 123 lemmas of f0..f30 compile in plain Lean, depend on no axioms, no `sorry`, no unmapped step.
  `Triv` -> `try rfl`; `Compute` -> `change`; lemma/hypothesis rewrites -> `conv => lhs; rw [..]`;
  induction with the quantified hypothesis -> `induction x generalizing y z`. Includes
  `f3 (f2 a b) = f2 (f3 b) (f3 a)` and `f3 (f3 a) = a` (reverse).

- Everything proved in the suite as Lean theorems (#53): `Export/Suite.lean`, `Generated/Suite.lean`
  (93 theorems: `lemascomp`, the 35 lemmas, the chains), plus `scripts/gate-compile.py`, the compile
  gate (found N, compiled N; negative test with a corrupted proof). One `lemascomp` lemma the system
  does not prove is reported, not exported. Still open for #53: the gate is not inside the discovery
  loop (a lemma still counts as found when its Lean theorem fails; the gate reports it), and only
  developments of the repository are exported, not arbitrary new ones.

- A development the exporter was not written against (#59): `Examples/Trees.lean`, `Generated/Trees.lean`.
  Polymorphic trees with `mirror`, `size`, `flatten`; the system finds 21 lemmas (including
  `mirror (mirror t) = t`) and all 21 compile (found 21, compiled 21, axiom-free). One data point, written
  by the same author as the exporter and in the same family (first-order, structural recursion);
  other families (mutual or nested types, higher-order functions) are untested.

- Traces (#39): `lake exe trace [dir] [first|all]` writes `enumerated.txt`, `conjectured.txt`,
  `attempted.txt`, `proved.txt` and `summary.txt` (default `trace/`, git-ignored, not committed).
  Everything is kept, not just the proved lemmas: 64 + 164 candidates, every conjecture of every
  batch (about 7 400 + 400 000), whether it was tried or skipped because a stored lemma rewrites it,
  and every attempt with its outcome; a failure says why (no rule applies / cycle cut / step budget
  exhausted). Each artifact is printed as the de Bruijn term and as Lean text; the 123 lemmas of the
  31 kept functions also link their Lean theorem. Two runs are byte-identical. Limits: the Lean text
  of a candidate or conjecture is printed, not compiled (only the kept functions and their lemmas
  are library modules); the full run takes minutes and about 150 MB.

## Next, in rough order

1. **Discharge the soundness assumptions mechanically.** `SigSound` is currently proved by
   hand per example. Derive it from a checked termination/totality argument (e.g. a
   structural-recursion check on definitions), and check `EnvClosed`/`DataWF` in the checker.
2. **Richer types.** Types are plain names; add type parameters (`List a`), function types,
   and typed induction over parameterised data. Keep nested-induction hypotheses by
   generalising instead of dropping them.
3. **Calculational output.** Print a checked certificate as a Dijkstra-style proof
   (`lhs = { hint } ...`), as the Haskell version prints LaTeX.
4. **Tactical search: beyond the list example.** `mainTactic` is ported (`Search.lean`);
   what is left is running it on the other lemma suites (#28) and the `paciencia` limit (#25).
5. **Strategic level.** Data types and functions are enumerated (#22); still to do: conjectures
   (#23, `conjeturas*`/`ample*`) and ranking lemmas ("ample", "deep").
6. **Binder-aware rewriting.** Allow rewriting and computing under binders and inside
   `case` alternatives.
7. **Reproduce Appendix B.** Rediscover the 31 functions f0..f30 from the thesis.
8. **Disproving.** Instantiate with values and compute, to discard false conjectures.
