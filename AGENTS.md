# AGENTS.md

Instructions for AI coding agents (and humans) working in this repository.
`CLAUDE.md` imports this file. Human-oriented detail is in `docs/DEVELOPMENT.md`.

## The one rule

**Every change needs an issue and a pull request.**

1. Open (or find) a GitHub issue that describes the change *before* writing code.
2. Work on a branch named `<type>/<short-slug>` (`feat`, `fix`, `docs`, `chore`,
   `refactor`, `test`).
3. Open one PR per issue. The PR description must contain `Closes #<issue>`.
4. Never push to `main`. Never merge your own PR unless the owner asks you to.

If you cannot create an issue or PR (missing credentials or tools), do not skip
the step silently: write the issue/PR text, push the branch if you can, and tell
the owner exactly what is missing.

## What this project is

A minimal Lean 4 implementation of the method in
[`juanmichelini/foundations`](https://github.com/juanmichelini/foundations):
mathematical methods treated as mathematical objects. The method is split into
three levels, and the code is split the same way:

| Level | Question | Code | Trusted? |
|---|---|---|---|
| Operational | what is possible? | `MathematicalMethodology/Operational/` | yes (small) |
| Tactical | how do we attempt it? | `MathematicalMethodology/Tactical/` | only `Cert.check` |
| Strategic | what is worth proving? | `MathematicalMethodology/Strategic/` (enumeration only so far) | no |
| Semantics | is the checker right? | `MathematicalMethodology/Semantics/` | proofs, not code |

- **Operational**: terms (de Bruijn), substitution, beta/case/delta computation.
- **Tactical**: `Cert` proof certificates and `Cert.check`, the checker. Tactics that
  *find* certificates are untrusted; only the checker must be right. `Tactical/Store.lean`
  (the lemma store: `fund`, dependencies, `Rec`) and `Tactical/Search.lean` (the port of
  `mainTactic`) are untrusted: nothing in `Cert.lean`, `Operational/` or `Semantics/` may
  import them. The search builds each next goal with the checker's own functions, so a
  bug there can only make it fail, never make a false statement pass.
- `Tactical/Prove.lean` is a faithful port of Haskell's `mainTactic`/`giveUp`/`prove` with
  `Proof` trees (names as metadata, induction hypotheses as quantified lemmas, fields as
  opaque constants, the cumulative step budget); `Strategic/FindLemmas.lean` is
  `findlemas`/`provell`. `Tactical/Search.lean` is the other search: it builds `Cert`s the
  checker can re-verify. Found lemmas are checked with it (`certify`).
- `Strategic/FirstSearch.lean`: `candidatosFstSel`/`namedFstSel`/`fstEnv`/`fstTEnv`/`fstRec`,
  including the binder renaming Haskell does when `f` becomes `f0`.
- `Strategic/SecondSearch.lean`: `candidatosSnd`/`candidatosSndSel`/`namedSndSel` (f3..f30).
  Together with the first search these are the 31 functions of the thesis' Appendix B.
- `Examples/TestEnv.lean` is *generated* from foundations' `Test.hs` (`scripts/haskell/TestEnv.hs`):
  environment, types, data types, the 35 lemmas and the names the definitions use.
  `Examples/TestSuite.lean` runs the suite and the lemma chains of `Test.hs`.
- **Strategic**: enumeration of data types, functions and conjectures. Untrusted.
  `Strategic/Enumerate.lean` (port of the enumeration in `Propose.hs`) works directly on the
  de Bruijn `Term` (no named syntax). Foundations names all constructors' fields from one
  pool, so atoms are counted by position (`Strategic/Syntax.lean`, `termAtoms`), and
  `Strategic/Show.lean` rebuilds the Haskell names for display. Its output is compared, in
  order, with a list printed by the original Haskell (`Examples/HaskellFst.lean`).
  Nothing trusted imports it.
- `Strategic/Conjecture.lean` ports the conjecture generation (`conjeturas*`, `ample*`,
  `instanceAny`). Terms are de Bruijn; foundations' variable *names* are kept as metadata
  (`PTT.vts`) because Appendix B prints them and `masOrd` orders atoms by name. Checked
  against dumps of the original Haskell (`fixtures/haskell/`, `scripts/haskell/`).
- **Export** (`MathematicalMethodology/Export/`, `Generated/`): prints data types and generated
  functions as plain Lean (#34). Untrusted display code. `lake exe export-lean >
  MathematicalMethodology/Generated/FstCandidates.lean` regenerates the committed file; it is a
  library module, so `lake build` compiles it, and a guard in `Examples/ExportCheck.lean`
  checks it equals the generator's output. `lake exe export-lean appendixB >
  MathematicalMethodology/Generated/AppendixB.lean` does the same for the 31 functions of
  Appendix B (checked by `lake exe results`, which runs the searches).
  `lake exe export-lean proofs` prints the lemmas of Appendix B as Lean theorems with the proofs
  the search found (`Generated/AppendixBProofs.lean`, #35); `lake build` makes Lean check them,
  `scripts/check-axioms.sh` and `scripts/check-negative-export.sh` run in CI.
- `Examples/` holds worked developments (currently `rev (rev xs) = xs`).
- `Pretty.lean`, `Report.lean` and `Results.lean` are display and reporting only; they are
  not trusted and nothing trusted may import them.

**Trusted-base rule:** anything that can make a false statement pass `Cert.check`
is trusted and gets extra care (tests that reject bad certificates, small diffs,
no cleverness). Search and enumeration code must never be imported by the
operational level or by `Cert.check`.

## Commands

```
lake build                          # builds everything and runs the #guard tests
lake exe results > results/report.md  # regenerates the committed report
```

There is no separate test runner: tests are `#guard` / `#eval` checks inside the
Lean files, so a successful `lake build` means the tests passed.

`results/report.md` is a deterministic, committed record of what the checker accepts
and rejects. CI regenerates it on a clean runner and **fails if it differs from the
committed copy**, so regenerate and commit it whenever behaviour changes. Do not edit
it by hand and do not add timestamps or hashes to it.

Toolchain: `lean-toolchain` pins the version (currently Lean 4.24.0).
If `elan` cannot reach `release.lean-lang.org` (restricted sandboxes), download
`lean-<version>-linux.zip` from the `leanprover/lean4` GitHub releases and put its
`bin/` on `PATH`; see `CLAUDE.md`.

## Definition of done

- `lake build` succeeds with no errors and no `sorry`.
- New behaviour has a `#guard` that passes **and** a `#guard` showing the checker
  rejects a wrong input (for anything touching `Cert.check`).
- The soundness proofs still compile (`lake build`), and `#print axioms` on
  `MM.Cert.check_sound` shows only standard axioms.
- `results/report.md` regenerated and committed if anything it reports changed.
- Docs updated if behaviour or structure changed (`README.md`, this file,
  `docs/ROADMAP.md`).
- PR description says what was and was not verified. Do not claim CI passed if
  you did not see it pass.

## Code conventions

- `autoImplicit` is off. Prefer structural recursion; avoid `partial` and `unsafe`
  in the trusted base.
- Free variables are de Bruijn indices; a `case` alternative of arity `n` binds `n`
  variables and variable `0` is the *last* constructor argument.
- Rewriting and computing only touch spine positions (application parts and
  `case` scrutinees), never binders or alternatives. Keep it that way until
  binder-aware rewriting is its own issue.
- `Semantics/` holds the proofs about the trusted base (`Cert.check_sound`). Changing
  `Cert.lean`, `Compute.lean` or `Term.lean` means keeping those proofs compiling;
  never weaken the theorem statements to make a change go through.
- Lemma rules only rewrite first-order terms and every instance is type-checked against
  `Ctx.sigs` (signatures of defined functions); `induct` requires a scoped statement and
  drops rigid rules. A new function needs a signature, and `SigSound` for it.
- Known gaps (do not paper over them): the soundness theorem assumes `EnvClosed`,
  `SigSound` and `DataWF` (proved per example, not checked by the checker); types are
  first-order names only; undeclared types are opaque. See `docs/ROADMAP.md`.

## Commits and PRs

- Small, focused commits; imperative subject line (`Add append_assoc certificate`).
- One logical change per PR. Stack PRs only when one truly depends on another, and
  say so in the description.
- PR description: what changed, why, how it was verified, what is left.
