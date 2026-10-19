#!/bin/sh
# Negative test for the proof export: Lean must REJECT a wrong theorem, whether the proof is
# the one of a true lemma or a corrupted one.  Exits 0 iff Lean rejects every case.
cd "$(dirname "$0")/.."
bad=0
check() {
  T="$(mktemp -t neg.XXXXXX).lean"
  printf '%s\n' "import MathematicalMethodology.Generated.AppendixB" "set_option linter.unusedVariables false" "namespace AppB" "$2" "end AppB" > "$T"
  if lake env lean "$T" > /dev/null 2>&1; then echo "FAIL: Lean accepted: $1"; bad=1; else echo "ok: Lean rejected: $1"; fi
}
check "false statement (f0 a O = O) with the proof of the true f0 a O = a" '
theorem bad1 (a : C_u_cR) : f0 a C_u_cR.C_u_cR_d0 = C_u_cR.C_u_cR_d0 := by
  induction a with
  | C_u_cR_d0 => change C_u_cR.C_u_cR_d0 = C_u_cR.C_u_cR_d0; try rfl
  | C_u_cR_d1 d ih_d =>
    change C_u_cR.C_u_cR_d1 (f0 d C_u_cR.C_u_cR_d0) = C_u_cR.C_u_cR_d1 d
    try (conv => lhs; rw [ih_d])
    try rfl'
check "true statement, induction case left unproved" '
theorem bad2 (a : C_u_cR) : f0 a C_u_cR.C_u_cR_d0 = a := by
  induction a with
  | C_u_cR_d0 => try rfl
  | C_u_cR_d1 d ih_d =>
    change C_u_cR.C_u_cR_d1 (f0 d C_u_cR.C_u_cR_d0) = C_u_cR.C_u_cR_d1 d
    try rfl'
check "false step: change to a different statement" '
theorem bad3 (a : C_u_cR) : f0 C_u_cR.C_u_cR_d0 a = a := by
  change C_u_cR.C_u_cR_d1 a = a
  try rfl'
# The compile gate must FAIL when a generated theorem does not compile (corrupted copy of the
# committed suite export), and must PASS on the committed file.
G="$(mktemp -t gate.XXXXXX).lean"
sed '/^theorem lemma_l9 /,/^theorem lemma_l10 /s/change Nat.S (suma a Nat.O) = Nat.S a/change Nat.S (suma a Nat.O) = Nat.O/' \
  MathematicalMethodology/Generated/Suite.lean > "$G"
if python3 scripts/gate-compile.py "$G" > /dev/null 2>&1; then echo "FAIL: the gate accepted a corrupted proof"; bad=1; else echo "ok: the gate rejected a corrupted proof"; fi
if python3 scripts/gate-compile.py MathematicalMethodology/Generated/Suite.lean > /dev/null 2>&1; then echo "ok: the gate accepted the committed suite"; else echo "FAIL: the gate rejected the committed suite"; bad=1; fi
exit $bad
