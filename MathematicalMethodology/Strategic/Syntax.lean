import MathematicalMethodology.Strategic.Util

/-!
# Named syntax for the strategic level

The enumeration of foundations works on *named* terms and on types, and its output order
depends on the names (`sort`, `nub`, fresh-variable choice).  To reproduce the same lists
this level keeps the Haskell representation: named variables, `case` alternatives
`((Con, [Var]), Term)`, and first-order types.  Converting to the de Bruijn `Term` of
`Operational/` is a separate step (issue #26); until then nothing here touches the
checker.
-/

namespace MM.Strategic

inductive NAtm where
  | var (v : String)
  | con (c : String)
  deriving BEq, DecidableEq, Repr

mutual
  inductive NTerm where
    | atm (a : NAtm)
    | app (f a : NTerm)
    | abs (v : String) (body : NTerm)
    | cas (scrut : NTerm) (alts : NAlts)
  inductive NAlts where
    | nil
    | cons (c : String) (vs : List String) (body : NTerm) (rest : NAlts)
end

mutual
  def NTerm.beq : NTerm → NTerm → Bool
    | .atm a, .atm b => a == b
    | .app f a, .app g b => f.beq g && a.beq b
    | .abs v t, .abs w u => v == w && t.beq u
    | .cas s as, .cas t bs => s.beq t && NAlts.beq as bs
    | _, _ => false
  def NAlts.beq : NAlts → NAlts → Bool
    | .nil, .nil => true
    | .cons c vs t r, .cons d ws u s => c == d && vs == ws && t.beq u && NAlts.beq r s
    | _, _ => false
end

instance : BEq NTerm := ⟨NTerm.beq⟩

def NTerm.var (v : String) : NTerm := .atm (.var v)
def NTerm.con (c : String) : NTerm := .atm (.con c)

/-- Build the alternatives of a `case` from a list. -/
def NAlts.ofList : List (String × List String × NTerm) → NAlts
  | [] => .nil
  | (c, vs, t) :: r => .cons c vs t (ofList r)

/-- Haskell `appParams (h, args)`. -/
def NTerm.mkApp (h : NTerm) (args : List NTerm) : NTerm :=
  args.foldl NTerm.app h

/-- Haskell `listParams`: head and arguments of an application spine. -/
def NTerm.listParams : NTerm → NTerm × List NTerm
  | .app f a => let (h, hs) := f.listParams; (h, hs ++ [a])
  | t => (t, [])

mutual
  /-- Haskell `termToAtm`: atoms in order of appearance (binders are skipped). -/
  def NTerm.atoms : NTerm → List NAtm
    | .atm a => [a]
    | .app f a => f.atoms ++ a.atoms
    | .abs _ b => b.atoms
    | .cas s as => s.atoms ++ NAlts.atoms as
  def NAlts.atoms : NAlts → List NAtm
    | .nil => []
    | .cons _ _ t r => t.atoms ++ NAlts.atoms r
end

/-- Haskell `contiene`. -/
def NTerm.contains (a : NAtm) (t : NTerm) : Bool := t.atoms.contains a

/-! ## Printing -/

mutual
  def NTerm.pp : NTerm → String
    | .atm (.var v) => v
    | .atm (.con c) => c
    | .app f a => s!"({f.pp} {a.pp})"
    | .abs v b => s!"(\\{v} -> {b.pp})"
    | .cas s as => s!"(case {s.pp} of \{{"; ".intercalate (NAlts.items as)}})"
  def NAlts.items : NAlts → List String
    | .nil => []
    | .cons c vs t r => s!"{" ".intercalate (c :: vs)} -> {t.pp}" :: NAlts.items r
end

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
abbrev TEnv := List (NTerm × Ty)

end MM.Strategic
