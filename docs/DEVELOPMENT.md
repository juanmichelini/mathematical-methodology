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

## Style

- No `sorry`. No `partial`/`unsafe` in the trusted base. `autoImplicit` is off.
- Prefer structural recursion; mutual inductives are fine.
- Document known limitations next to the code they affect.

## Review checklist

- Is there an issue, and does the PR close it?
- Does it build, and was that actually observed?
- If it touches the trusted base: could it make a false statement pass? Is there a
  negative test?
- Are docs and `docs/ROADMAP.md` updated?
