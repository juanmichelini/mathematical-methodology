# Roadmap

Each item below should become an issue before work starts (see `AGENTS.md`).

## Done (v0)

- Operational level: de Bruijn terms, substitution, beta/case/delta, `computeSafe`/`computeWide`.
- Tactical level: `Affirm`, `Rule`, `Cert`, `Cert.check`, `checkDevelopment`.
- Example: `append_nil`, `append_assoc`, `rev_append`, `rev_rev` as checked certificates.
- Deterministic results report (`lake exe results`), committed in `results/` and verified by CI.

## Next, in rough order

1. **Soundness theorem for `Cert.check`.** Define a semantics (equality of terms under
   the computation rules plus typed induction) and prove: if `check` succeeds, the
   `Affirm` holds. This is what makes the trusted base *verified*.
2. **Simple types.** Type terms, make matching typed, and close the untyped-matching gap
   noted in `Tactical/Cert.lean`.
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
