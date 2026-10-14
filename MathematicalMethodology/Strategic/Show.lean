import MathematicalMethodology.Strategic.Syntax

/-!
# Showing generated functions

Display only.  Prints a generated function the way foundations' `toCLI` does, so that the
output can be compared with the Haskell run.  The de Bruijn term has no names; the ones
foundations chose are determined by position: for a function with `k` parameters the
parameters are `a, b, c, …` read from the *last* parameter backwards, and the fields of
every alternative are named after them (`k`-th letter onwards, left to right).
-/

namespace MM.Strategic

/-- `a … z`, then `v26`, `v27`, … (distinct, never reused). -/
def letter (n : Nat) : String :=
  if n < 26 then ("abcdefghijklmnopqrstuvwxyz".toList.getD n 'a').toString else s!"v{n}"

mutual
  /-- `k` parameters, `n` = arity of the enclosing alternative. -/
  def showTerm (k n : Nat) : Term → String
    | .var i => if i < n then letter (k + (n - 1 - i)) else letter (i - n)
    | .con c => c
    | .const f => f
    | .app x (.app y z) => showTerm k n x ++ " (" ++ showTerm k n (.app y z) ++ ")"
    | .app x y => showTerm k n x ++ " " ++ showTerm k n y
    | .abs b => "\\_ -> " ++ showTerm k n b
    | .cas s alts => "case " ++ showTerm k n s ++ " of { " ++ showAlts k alts ++ "}"

  def showAlts (k : Nat) : Alts → String
    | .nil => ""
    | .alt c n b rest =>
      c ++ String.join ((List.range n).map fun j => " " ++ letter (k + j)) ++ " -> " ++
        showTerm k n b ++ "; " ++ showAlts k rest
end

/-- Number of leading lambdas. -/
def funArity : Term → Nat
  | .abs b => 1 + funArity b
  | _ => 0

/-- The term under the leading lambdas. -/
def funBody : Term → Term
  | .abs b => funBody b
  | t => t

/-- Haskell `toCLI` of a generated function `\p… -> case …`. -/
def showFun (t : Term) : String :=
  let k := funArity t
  String.join ((List.range k).map fun i => "\\" ++ letter (k - 1 - i) ++ " -> ") ++
    showTerm k 0 (funBody t)

/-! ## Open terms with variable names (conjectures) -/

/-- `toCLI` of a binder-free term whose free variable `i` is called `names[i]`. -/
def showNamed (names : List String) : Term → String
  | .var i => names.getD i s!"?{i}"
  | .con c => c
  | .const f => f
  | .app x (.app y z) => showNamed names x ++ " (" ++ showNamed names (.app y z) ++ ")"
  | .app x y => showNamed names x ++ " " ++ showNamed names y
  | _ => "<binder>"

end MM.Strategic
