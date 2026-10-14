# Development guidelines

## Workflow: issue, branch, PR

Every change, however small, goes through an issue and a pull request.

1. **Issue.** Open one using the *Task* template. State the goal, the level
   (operational / tactical / strategic / tooling / docs), whether it touches the
   trusted base, and acceptance criteria.
2. **Branch.** From an up-to-date `main`: `git switch -c <type>/<short-slug>`
   with type one of `feat`, `fix`, `docs`, `chore`, `refactor`, `test`.
3. **Work.** Small commits with imperative subjects. Run `lake build` often.
4. **PR.** One PR per issue, with `Closes #N` in the description. Fill in the template.
5. **Review and merge.** Another person (or the owner) reviews; use squash merge.
   Never push to `main`.

## Architecture in one page

Three levels, taken from the thesis:

- **Operational** (`MathematicalMethodology/Operational/`): what is possible. Terms,
  substitution, computation. Small and trusted.
- **Tactical** (`MathematicalMethodology/Tactical/`): how we attempt things. `Cert` is a
  proof certificate; `Cert.check` re-verifies it using the operational level. Finding
  certificates (tactics) is untrusted; checking them is trusted.
- **Strategic** (`MathematicalMethodology/Strategic/`, to come): what is worth proving.
  Enumerates and ranks. Untrusted.

The dependency direction is strictly Strategic -> Tactical -> Operational. The trusted
base (operational level plus `Cert.check`) must not import search or enumeration code.

## Testing

Tests are `#guard` and `#eval` lines inside the Lean files; `lake build` runs them.
For anything that touches `Cert.check`, add both:

- a positive test (a good certificate is accepted), and
- a negative test (a wrong statement, a bad rule index, a missing case... is rejected).

A checker that only has positive tests has not been tested.

### Results report

`lake exe results > results/report.md` writes a markdown report: every lemma with its
statement, certificate size and result, and every negative test with the checker's
rejection message. The report is committed and deterministic (no timestamps, hashes or
timings). CI regenerates it on a clean runner and fails if it differs from the committed
copy, and uploads it as the `results` artifact. If you change what the checker accepts or
rejects, regenerate and commit the report in the same PR.

Negative tests live in `Examples/*.lean` as data (`negatives`), so the `#guard` and the
report always agree.

## Style

- No `sorry`. No `partial`/`unsafe` in the trusted base. `autoImplicit` is off.
- Prefer structural recursion; mutual inductives are fine.
- Document known limitations next to the code they affect.

## Review checklist

- Is there an issue, and does the PR close it?
- Does it build, and was that actually observed?
- If it touches the trusted base: could it make a false statement pass? Is there a
  negative test?
- Is `results/report.md` regenerated if the checker's behaviour changed?
- Are docs and `docs/ROADMAP.md` updated?

## Comparing with the Haskell

Parity with `juanmichelini/foundations` is checked against output of the original program,
not only its committed `results/*.txt`. Install GHC (`brew install ghc`), then print what you
want to compare from `foundations/code`, for example the first-search candidates:

```
cat > Fst.hs <<'HS'
module Fst where
import qualified Main as M
import PrettyPrint
import Type
ppTy :: Type -> String
ppTy (TAtm (TCon c)) = c
ppTy (TAtm (TVar v)) = v
ppTy (TBin TCom a b) = "(" ++ ppTy a ++ " -> " ++ ppTy b ++ ")"
fstMain :: IO ()
fstMain = mapM_ (\(e,t) -> putStrLn (toCLI e ++ "  ::  " ++ ppTy t)) M.candidatosFst
HS
ghc -O0 -i<foundations>/code -outputdir build -main-is Fst.fstMain Fst.hs -o fst && ./fst
```

`Examples/HaskellFst.lean` holds that output (64 lines, backslashes escaped) and
`Examples/Enumeration.lean` guards that the Lean list is identical to it, in order.

### Oracle scripts and fixtures

`scripts/haskell/` has the Haskell programs that print what the Lean port must reproduce, and
`scripts/haskell/build.sh <foundations-dir> <Module> [out]` builds and runs one:

| script | prints | Lean side |
|---|---|---|
| `Fst.hs` | the 64 first-search candidates | `Examples/HaskellFst.lean` (committed) |
| `Conj.hs` | `plemas` for each candidate (8222 lines) | `fixtures/haskell/conj_fst.txt`, guard in `Examples/ConjecturesFst.lean` |
| `TestConj.hs` | `plemas`/`pfindlemasAll` for `Test.hs` functions (89215 lines, 6 MB) | hash in `fixtures/haskell/conj_test.fnv`, checked by `lake exe haskell-check` |
| `ProveTrace.hs` | `provell` trace for each candidate: tried conjectures, complete or not, smallest budget, lemma chosen (3358 lines) | `fixtures/haskell/prove_fst.txt`, guard in `Examples/ProveFst.lean` |
| `TestEnv.hs` | `Test.env`/`tenv`/`datas` as de Bruijn Lean | `Examples/TestEnv.lean` (generated) |

To diff a large dump in full: `scripts/haskell/build.sh <foundations> TestConj /tmp/h.txt`,
`lake exe haskell-check --dump conj_test > /tmp/l.txt`, `diff /tmp/h.txt /tmp/l.txt`.
Caveat: Lake does not track files read with `include_str`; after changing a fixture, delete
the importing module's build products (for example `find .lake/build -name 'HaskellCheck*' -delete`).
