# mathematical-methodology

A minimal [Lean 4](https://lean-lang.org) implementation of the method in
[`juanmichelini/foundations`](https://github.com/juanmichelini/foundations):
*some mathematical methods can be treated as mathematical objects.*

The method has three levels, and so does the code:

| Level | Question | Where | Trusted |
|---|---|---|---|
| Operational | what is possible? | `MathematicalMethodology/Operational/` | yes |
| Tactical | how do we attempt it? | `MathematicalMethodology/Tactical/` | `Cert.check` only |
| Strategic | what is worth proving? | `MathematicalMethodology/Strategic/` (enumeration so far) | no |

Proofs are *certificates* (`Cert`) that a small checker re-verifies. The headline
example, in `Examples/Lists.lean`, checks `rev (rev xs) = xs` together with the lemmas
it needs (`append_nil`, `append_assoc`, `rev_append`).

## Build

```
lake build                            # builds and runs the #guard tests
lake exe results > results/report.md  # regenerate the committed report
```

Tests are `#guard` checks inside the Lean files, so a successful build means they pass.
[`results/report.md`](results/report.md) records what the checker accepts and rejects;
CI regenerates it and fails if the committed copy is stale.

## Status

Early, but the checker is **proved sound**: `Cert.check_sound`
(`Semantics/CheckSound.lean`) says that if a certificate is accepted then the statement
holds, as a `Conv` equation (delta, beta, case), for every substitution of *values*
for its variables.  The theorem is conditional on three explicit assumptions about the
checker's context (definitions are closed, declared function signatures are right, data
type names are unique); `Examples/ListsSound.lean` proves them for the list example,
which gives `development_valid` and `revRev_valid`.  Not proved: that the defined
functions are total in general (it is an assumption per development), termination
of computation, or anything about the untrusted search and strategy levels.
See [`docs/ROADMAP.md`](docs/ROADMAP.md).

## Contributing

Every change needs an issue and a pull request. See [`AGENTS.md`](AGENTS.md) and
[`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md).
