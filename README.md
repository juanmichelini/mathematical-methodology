# mathematical-methodology

A minimal [Lean 4](https://lean-lang.org) implementation of the method in
[`juanmichelini/foundations`](https://github.com/juanmichelini/foundations):
*some mathematical methods can be treated as mathematical objects.*

The method has three levels, and so does the code:

| Level | Question | Where | Trusted |
|---|---|---|---|
| Operational | what is possible? | `MathematicalMethodology/Operational/` | yes |
| Tactical | how do we attempt it? | `MathematicalMethodology/Tactical/` | `Cert.check` only |
| Strategic | what is worth proving? | to come | no |

Proofs are *certificates* (`Cert`) that a small checker re-verifies. The headline
example, in `Examples/Lists.lean`, checks `rev (rev xs) = xs` together with the lemmas
it needs (`append_nil`, `append_assoc`, `rev_append`).

## Build

```
lake build
```

Tests are `#guard` checks inside the Lean files, so a successful build means they pass.

## Status

Early. The checker is tested but has no soundness proof yet, and matching is untyped.
See [`docs/ROADMAP.md`](docs/ROADMAP.md).

## Contributing

Every change needs an issue and a pull request. See [`AGENTS.md`](AGENTS.md) and
[`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md).
