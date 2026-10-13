import MathematicalMethodology.Strategic.Util
import MathematicalMethodology.Operational.Term

/-!
# Syntax of the strategic level

The strategic level works directly on the de Bruijn `Term` of `Operational/` (issue #33).
Foundations uses named variables; two facts about its enumeration make the translation
mechanical:

* a generated function is `\p₁ … \pₖ -> case p₁ of { C x₁ … xₙ -> body; … }`, and a body
  is an application of parameters, fields, constructors and the function itself; there are
  no other binders;
* fields of *all* constructors draw their names from the same pool, so field `j` of one
  constructor is the same atom (for `repiteAtmHasta`) as field `j` of another.

So inside an alternative of arity `n` under `k` parameters, `var i` is field `n-1-i` when
`i < n` and parameter `k-1-(i-n)` otherwise (`Atm`, below).  The function being defined
is `.const "f"`.

Types are first-order, as in the prototype.  Untrusted: nothing in `Operational/`,
`Cert.lean` or `Semantics/` imports this file.
-/

namespace MM.Strategic

/-! ## Types -/

/-- First-order types of the prototype: variables, constructors, arrows. -/
inductive Ty where
  | var (v : String)
  | con (c : String)
  | com (a b : Ty)
  deriving BEq, DecidableEq, Repr

def Ty.pp : Ty → String
  | .var v => v
  | .con c => c
  | .com a b => s!"({a.pp} -> {b.pp})"

/-- Haskell `returnsTypeM t o`: if `o = a₁ → … → aₖ → t`, the list `[a₁,…,aₖ]`. -/
def Ty.returnsM (t : Ty) : Ty → Option (List Ty)
  | o@(.com x y) => if t == o then some [] else (returnsM t y).map (x :: ·)
  | o => if t == o then some [] else none

/-- Haskell `parsAndRet`: parameters and final result. -/
def Ty.parsAndRet : Ty → List Ty × Ty
  | .com x y => let (ps, r) := y.parsAndRet; (x :: ps, r)
  | t => ([], t)

/-- Haskell `lastRet`. -/
def Ty.lastRet : Ty → Ty
  | .com _ y => y.lastRet
  | t => t

/-- A data type in Haskell style: name and constructors with field types. -/
abbrev DatasH := String × List (String × List Ty)

/-- Haskell `datasH2C`: constructors with their full (curried) types. -/
def DatasH.toC (d : DatasH) : List (String × Ty) :=
  d.2.map fun (c, fs) => (c, fs.foldr Ty.com (Ty.con d.1))

/-- Typing environment of the prototype: terms with their types. -/
abbrev TEnv := List (Term × Ty)

/-! ## Atoms

The atoms of a generated function, as Haskell sees them (`termToAtm`): a parameter or a
field is identified by its *position from the left* (not by its de Bruijn index, which
depends on the arity of the enclosing alternative). -/

inductive Atm where
  | param (i : Nat)
  | field (j : Nat)
  | con (c : String)
  | const (f : String)
  deriving BEq, DecidableEq, Repr

-- Atoms of `t` in order of appearance, for a function with `k` parameters, `n` being the
-- arity of the enclosing alternative (`0` outside any).  Binders are skipped.
mutual
  def termAtoms (k : Nat) : Nat → Term → List Atm
    | n, .var i =>
      if i < n then [.field (n - 1 - i)] else [.param (k - 1 - (i - n))]
    | _, .con c => [.con c]
    | _, .const f => [.const f]
    | n, .app f a => termAtoms k n f ++ termAtoms k n a
    | n, .abs b => termAtoms k n b
    | n, .cas s alts => termAtoms k n s ++ altsAtoms k alts

  def altsAtoms (k : Nat) : Alts → List Atm
    | .nil => []
    | .alt _ n b rest => termAtoms k n b ++ altsAtoms k rest
end

/-- Does the term mention this constant (Haskell `contiene (Var f)`)? -/
def mentions (f : String) (t : Term) : Bool :=
  (termAtoms 0 0 t).contains (.const f)

end MM.Strategic
