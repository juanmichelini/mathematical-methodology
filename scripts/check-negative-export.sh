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
# The same for the export of the checker's own certificates (Generated/Lists.lean).
checkL() {
  T="$(mktemp -t neg.XXXXXX).lean"
  printf '%s\n' "import MathematicalMethodology.Generated.Lists" "set_option linter.unusedVariables false" "namespace ListsEx" "$2" "end ListsEx" > "$T"
  if lake env lean "$T" > /dev/null 2>&1; then echo "FAIL: Lean accepted: $1"; bad=1; else echo "ok: Lean rejected: $1"; fi
}
checkL "false statement (append x nil = nil) with the proof of append_nil" '
theorem badL1 {ty_Elem : Type} (x : ExList ty_Elem) :
    append x (ExList.nil : ExList ty_Elem) = (ExList.nil : ExList ty_Elem) := by
  induction x with
  | nil =>
    change (ExList.nil : ExList ty_Elem) = (ExList.nil : ExList ty_Elem)
    try rfl
  | cons f0 f1 ih_f1 =>
    change ExList.cons f0 (append f1 (ExList.nil : ExList ty_Elem)) = (ExList.nil : ExList ty_Elem)
    conv => lhs; rw [ih_f1]
    try rfl'
checkL "true statement (rev (rev x) = x), induction case left unproved" '
theorem badL2 {ty_Elem : Type} (x : ExList ty_Elem) : rev (rev x) = x := by
  induction x with
  | nil => try rfl
  | cons f0 f1 ih_f1 => try rfl'
checkL "a step the checker would not accept: rewrite with a lemma that does not apply" '
theorem badL3 {ty_Elem : Type} (x : ExList ty_Elem) : rev x = x := by
  conv => lhs; rw [rev_rev x]'
exit $bad
