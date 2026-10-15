import MathematicalMethodology.Generated.AppendixB

/-!
# The functions of Appendix B, running in Lean

`Generated/AppendixB.lean` holds f0 … f30 as plain Lean; it is a module of the library, so
`lake build` compiles it (Lean accepts the definitions and their structural recursion).  Here
a few of them run: f0 is addition, f1 is addition with a successor base, f2 is list append
and f3 is `reverse` (it calls f2).
-/

namespace MM.Examples.ExportAppendixB

open AppB

private def n : Nat → C_u_cR
  | 0 => .C_u_cR_d0
  | k + 1 => .C_u_cR_d1 (n k)

private def l (xs : List Nat) : C_u_ca_uR C_u_cR :=
  xs.foldr (fun x t => .C_u_ca_uR_d1 (n x) t) .C_u_ca_uR_d0

#guard f0 (n 2) (n 3) = n 5
#guard f1 (n 2) (n 3) = n 6
#guard f2 (l [1, 2]) (l [3]) = l [1, 2, 3]
#guard f3 (l [1, 2, 3]) = l [3, 2, 1]
#guard f3 (f3 (l [4, 5, 6, 7])) = l [4, 5, 6, 7]
#guard f3 (f2 (l [1, 2]) (l [3])) = f2 (f3 (l [3])) (f3 (l [1, 2]))

end MM.Examples.ExportAppendixB
