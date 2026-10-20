#!/usr/bin/env python3
"""The compile gate: a proof the system found counts only if Lean accepts its theorem.

usage: gate-compile.py FILE.lean

Compiles FILE with `lake env lean`, attributes every error (and every use of `sorry`) to the
theorem it occurs in, and prints `found N, compiled M` and the failing theorems.  Exit status 0
iff every theorem compiles (and there is at least one).  Run from the repository root.
"""
import re, subprocess, sys

path = sys.argv[1]
lines = open(path, encoding="utf-8").read().split("\n")
thm_at = []  # (line number, name)
for i, l in enumerate(lines, 1):
    m = re.match(r"theorem (\S+)", l)
    if m:
        thm_at.append((i, m.group(1)))

def owner(line):
    cur = None
    for (n, name) in thm_at:
        if n <= line:
            cur = name
    return cur

r = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True)
out = r.stdout + r.stderr
failed = {}
other = []
for m in re.finditer(r"^(.*?):(\d+):(\d+): (error|warning): (.*)$", out, re.M):
    _, ln, _, kind, msg = m.groups()
    if kind == "error" or "sorry" in msg:
        t = owner(int(ln))
        if t is None:
            other.append(msg)
        else:
            failed.setdefault(t, msg)
if r.returncode != 0 and not failed and not other:
    other.append(out.strip()[:500] or "lean failed")

found = len(thm_at)
ok = found - len(failed)
print(f"{path}: found {found}, compiled {ok}")
if failed or other:
    print("  INVARIANT VIOLATED (should not happen): the system proved these lemmas, so Lean must accept their theorems")
for t, msg in failed.items():
    print(f"  FAILED {t}: {msg}")
for msg in other:
    print(f"  FAILED (outside any theorem): {msg}")
sys.exit(0 if found > 0 and not failed and not other else 1)
