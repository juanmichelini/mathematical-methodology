import MathematicalMethodology.Tactical.Cert

/-!
# Pretty printing

Display only; **not** part of the trusted base. Nothing in `Operational/` or
`Cert.check` depends on this file.

De Bruijn indices are shown with names: free variables follow the context of the
statement (`x`, `y`, `z`, ...), variables bound by `λ` are `b<depth>` and variables
bound by `case` alternatives are `a<depth>`.
-/

namespace MM

/-- Name of free variable number `i` of a statement. -/
def freeName (i : Nat) : String :=
  match ["x", "y", "z", "w", "u", "v"][i]? with
  | some s => s
  | none => s!"x{i}"

def Term.isAtom : Term → Bool
  | .app .. | .abs .. | .cas .. => false
  | _ => true

/-- Names for the variables bound by an alternative of arity `n`: variable `0`
is the last constructor argument. -/
def binderNames (names : List String) (n : Nat) : List String :=
  (List.range n).map (fun k => s!"a{names.length + (n - 1 - k)}") ++ names

def patternNames (names : List String) (n : Nat) : List String :=
  (List.range n).map fun k => s!"a{names.length + k}"

mutual
  def Term.pp (names : List String) : Term → String
    | .var i =>
      match names[i]? with
      | some s => s
      | none => freeName (i - names.length)
    | .con c => c
    | .const f => f
    | .app f a =>
      let sa := a.pp names
      f.pp names ++ " " ++ (if a.isAtom then sa else "(" ++ sa ++ ")")
    | .abs b =>
      let n := s!"b{names.length}"
      "λ" ++ n ++ ". " ++ b.pp (n :: names)
    | .cas s alts => "case " ++ s.pp names ++ " of { " ++ alts.pp names ++ " }"

  def Alts.pp (names : List String) : Alts → String
    | .nil => ""
    | .alt c n b rest =>
      let pat := String.intercalate " " (c :: patternNames names n)
      let here := pat ++ " → " ++ b.pp (binderNames names n)
      match rest with
      | .nil => here
      | _ => here ++ " | " ++ rest.pp names
end

/-- `∀ (x : List) (y : List). lhs = rhs` -/
def Affirm.pp (a : Affirm) : String :=
  let binders :=
    (a.ctx.zipIdx).map fun (ty, i) => s!"({freeName i} : {ty})"
  let body := a.lhs.pp [] ++ " = " ++ a.rhs.pp []
  if binders.isEmpty then body
  else "∀ " ++ String.intercalate " " binders ++ ". " ++ body

mutual
  /-- Number of steps in a certificate (every node counts as one). -/
  def Cert.size : Cert → Nat
    | .refl => 1
    | .compute _ rest => 1 + rest.size
    | .rewrite _ _ _ rest => 1 + rest.size
    | .induct _ cases => 1 + cases.size

  def Certs.size : Certs → Nat
    | .nil => 0
    | .cons c rest => c.size + rest.size
end

end MM
