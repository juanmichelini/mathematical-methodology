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
  port of `Rec`, `fund`, `dependencies`, `addAffirm` from `Prove.hs`; #24).

## Next, in rough order

1. **Discharge the soundness assumptions mechanically.** `SigSound` is currently proved by
   hand per example. Derive it from a checked termination/totality argument (e.g. a
   structural-recursion check on definitions), and check `EnvClosed`/`DataWF` in the checker.
2. **Richer types.** Types are plain names; add type parameters (`List a`), function types,
   and typed induction over parameterised data. Keep nested-induction hypotheses by
   generalising instead of dropping them.
3. **Calculational output.** Print a checked certificate as a Dijkstra-style proof
   (`lhs = { hint } ...`), as the Haskell version prints LaTeX.
4. **Tactical search.** Port `mainTactic` (Trivialize, Compute, Fundamentalize, Reorder,
   Induction) as an untrusted search that produces `Cert`s.
5. **Strategic level.** Enumerate data types, functions and conjectures (`Propose.hs`)
   and rank lemmas ("ample", "deep").
6. **Binder-aware rewriting.** Allow rewriting and computing under binders and inside
   `case` alternatives.
7. **Reproduce Appendix B.** Rediscover the 31 functions f0..f30 from the thesis.
8. **Disproving.** Instantiate with values and compute, to discard false conjectures.
