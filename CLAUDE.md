@AGENTS.md

# Claude-specific notes

Everything in `AGENTS.md` applies. In particular: **every change needs an issue and a
PR**, and nothing goes to `main` directly.

## Setting up Lean in a restricted sandbox

`elan` downloads toolchains from `release.lean-lang.org`, which is blocked in some
sandboxes (the egress proxy returns 403). `github.com` release assets are usually
reachable, so install the pinned toolchain by hand:

```
V=$(sed 's#.*:v##' lean-toolchain)          # e.g. 4.24.0
curl -fL -o lean.zip https://github.com/leanprover/lean4/releases/download/v$V/lean-$V-linux.zip
python3 -I -c "import zipfile; zipfile.ZipFile('lean.zip').extractall('.')"
export PATH="$PWD/lean-$V-linux/bin:$PATH"
lake build
```

Use the `.zip`, not the `.tar.zst`: `zstd` is often missing and `pip` may not be able
to fetch `zstandard`. Extract outside the repository (or into an ignored directory);
never commit toolchains.

## Working style

- Read `docs/ROADMAP.md` first; pick or create an issue from it.
- Keep the trusted base small. If a change touches `Cert.check`, add a negative test.
- When you finish, report what you ran (`lake build` output) and what you could not
  run (for example CI). Do not claim more than you saw.
- `gh` may be unauthenticated in a session. If so, say so and hand over ready-to-paste
  issue and PR text instead of skipping them.
