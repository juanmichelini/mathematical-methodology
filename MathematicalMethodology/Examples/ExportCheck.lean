import MathematicalMethodology.Export.Lean
import MathematicalMethodology.Examples.Enumeration
import MathematicalMethodology.Generated.FstCandidates

/-!
# Export to Lean: tests

* the committed `Generated/FstCandidates.lean` equals what the generator prints (and, being
  a module of the library, it is compiled by `lake build`: Lean itself accepts all 64
  candidates, including their structural recursion);
* the exported functions run in real Lean and compute what the prototype's functions are
  supposed to (`suma`, list `append`).
-/

namespace MM.Examples.ExportCheck

open MM MM.Strategic MM.Export MM.Examples.Enumeration

/-! ## The generator on a small example (`Nat`, `suma`) -/

private def nat : DatasH := datas[1]!

#guard exportData [nat] nat =
"inductive C_u_cR where
  | C_u_cR_d0 : C_u_cR
  | C_u_cR_d1 : C_u_cR → C_u_cR
  deriving DecidableEq, Repr
"

-- `\b -> \a -> case b of { O -> a; S c -> S (f c a) }`, named `suma`
private def sumaTerm : Term :=
  .abs (.abs (.cas (.var 1)
    (.alt "C_,R.0" 0 (.var 0) (.alt "C_,R.1" 1 (.app (.con "C_,R.1") (.app (.app (.const "f") (.var 0)) (.var 1))) .nil))))

#guard exportFun [nat] "suma" (.com (.con "C_,R") (.com (.con "C_,R") (.con "C_,R"))) sumaTerm =
"def suma (b : C_u_cR) (a : C_u_cR) : C_u_cR :=
  match b with
  | C_u_cR.C_u_cR_d0 => a
  | C_u_cR.C_u_cR_d1 c => C_u_cR.C_u_cR_d1 (suma c a)
"

-- names are sanitised injectively
#guard sanitize "C_,R.1" = "C_u_cR_d1"
#guard sanitize "C_,a_R" = "C_u_ca_uR"
#guard sanitize "C_,R" != sanitize "C_u,R"

-- type variables become parameters
#guard dataParams (datas[3]!) = ["a"]
#guard dataParams nat = []

/-! ## The committed file is the generator's output -/

#guard fstFile == include_str "../Generated/FstCandidates.lean"

-- one `def` per candidate
#guard ((fstFile.splitOn "\ndef ").length - 1) = candidatosFst.length

/-! ## Running the exported functions in Lean -/

open Gen

private def n : Nat → C_u_cR
  | 0 => .C_u_cR_d0
  | k + 1 => .C_u_cR_d1 (n k)

-- candidate 22 is `suma` (foundations: `\b -> \a -> case b of {O -> a; S c -> S (f c a)}`)
#guard fstLines[22]! = "\\b -> \\a -> case b of { C_,R.0 -> a; C_,R.1 c -> C_,R.1 (f c a); }  ::  (C_,R -> (C_,R -> C_,R))"
#guard fstCand22 (n 2) (n 3) = n 5
#guard fstCand22 (n 0) (n 4) = n 4

private def l (xs : List Nat) : C_u_ca_uR C_u_cR :=
  xs.foldr (fun x t => .C_u_ca_uR_d1 (n x) t) .C_u_ca_uR_d0

-- candidate 60 is list append
#guard fstLines[60]! = "\\b -> \\a -> case b of { C_,a_R.0 -> a; C_,a_R.1 c d -> C_,a_R.1 c (f d a); }  ::  (C_,a_R -> (C_,a_R -> C_,a_R))"
#guard fstCand60 (l [1, 2]) (l [3]) = l [1, 2, 3]

end MM.Examples.ExportCheck
