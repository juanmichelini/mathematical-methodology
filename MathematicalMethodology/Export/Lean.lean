import MathematicalMethodology.Strategic.Enumerate
import MathematicalMethodology.Strategic.Show

/-!
# Export to plain Lean

Prints data types and generated functions as Lean source that compiles and runs on its own
(no imports, no support library): each `DatasH` becomes an `inductive`, each function a
`def` with a `match`.  Untrusted display code (issue #34); nothing trusted imports it.

* Names are sanitised injectively: `_ ↦ _u`, `, ↦ _c`, `. ↦ _d`, so `C_,R.1` is `C_u_cR_d1`.
* Type variables of a data type (`a` in `C_,a`) become type parameters, written `ty_a` so
  that they never clash with the names of values (`a`, `b`, …).  A function mentions every
  type variable of its signature as an implicit parameter; all occurrences of `a` are the
  same type, as in the prototype.
* Recursion is structural on the first parameter (the generator only recurses on fields of
  the scrutinee), so Lean's own termination check accepts it.
-/

namespace MM.Export

open MM.Strategic

/-- Injective map from the prototype's names to Lean identifiers. -/
def sanitize (s : String) : String :=
  let body := String.join (s.toList.map fun c =>
    if c.isAlphanum then c.toString
    else if c == '_' then "_u"
    else if c == ',' then "_c"
    else if c == '.' then "_d"
    else s!"_x{c.toNat}")
  if body.front.isDigit then "n" ++ body else body

def tyVars : Ty → List String
  | .var v => [v]
  | .con _ => []
  | .com a b => tyVars a ++ tyVars b

/-- Type parameters of a data type: its type variables, in order of first occurrence. -/
def dataParams (d : DatasH) : List String :=
  (d.2.flatMap fun (_, fs) => fs.flatMap tyVars).eraseDups

def paramName (v : String) : String := "ty_" ++ sanitize v

/-- Type parameters a signature needs: those of the data types it mentions, and its own
type variables. -/
def sigParams (ds : List DatasH) : Ty → List String
  | .var v => [v]
  | .con c => match ds.find? (·.1 == c) with
    | some d => dataParams d
    | none => []
  | .com a b => sigParams ds a ++ sigParams ds b

/-- A type, with data types applied to their parameters. -/
def renderTy (ds : List DatasH) : Ty → String
  | .var v => paramName v
  | .con c =>
    match ds.find? (·.1 == c) with
    | some d => String.intercalate " " (sanitize c :: (dataParams d).map paramName)
    | none => sanitize c
  | .com a b => s!"({renderTy ds a} → {renderTy ds b})"

/-- Qualified Lean name of a constructor. -/
def ctorName (ds : List DatasH) (c : String) : String :=
  match ds.find? fun d => d.2.any (·.1 == c) with
  | some d => sanitize d.1 ++ "." ++ sanitize c
  | none => sanitize c

def exportData (ds : List DatasH) (d : DatasH) : String :=
  let ps := dataParams d
  let head := String.intercalate " " (sanitize d.1 :: ps.map fun p => s!"({paramName p} : Type)")
  let res := String.intercalate " " (sanitize d.1 :: ps.map paramName)
  let ctors := d.2.map fun (c, fs) =>
    let args := fs.map fun t => renderTy ds t ++ " → "
    s!"  | {sanitize c} : {String.join args}{res}"
  s!"inductive {head} where\n{"\n".intercalate ctors}\n  deriving DecidableEq, Repr\n"

mutual
  /-- `self` is the Lean name of the function being defined (`.const "f"`); `k` is its number of
  parameters and `ctx` the names of the variables in scope, de Bruijn index 0 first (the
  parameters, then the fields of every enclosing alternative).  A field of the `j`-th
  enclosing-and-own alternative variable is called `letter (k + j)`, so nested `case`s never
  reuse a name. -/
  def leanTerm (ds : List DatasH) (self : String) (k : Nat) (ctx : List String) : Term → String
    | .var i => ctx.getD i s!"_v{i}"
    | .con c => ctorName ds c
    | .const f => if f == "f" then self else sanitize f
    | .app x (.app y z) =>
      leanTerm ds self k ctx x ++ " (" ++ leanTerm ds self k ctx (.app y z) ++ ")"
    | .app x y => leanTerm ds self k ctx x ++ " " ++ leanTerm ds self k ctx y
    | .abs b => "fun _ => " ++ leanTerm ds self k ctx b
    | .cas s alts =>
      s!"(match {leanTerm ds self k ctx s} with\n{(leanAlts ds self k ctx alts).trimRight})"

  def leanAlts (ds : List DatasH) (self : String) (k : Nat) (ctx : List String) : Alts → String
    | .nil => ""
    | .alt c n b rest =>
      let fields := (List.range n).map fun j => letter (k + (ctx.length - k) + j)
      let pat := String.join (fields.map (" " ++ ·))
      s!"| {ctorName ds c}{pat} => {leanTerm ds self k (fields.reverse ++ ctx) b}\n{leanAlts ds self k ctx rest}"
end

/-- A `match` is parenthesised wherever it occurs, so that a nested one does not swallow the
alternatives that follow it; the outermost one needs no parentheses. -/
def unparen (t : Term) (s : String) : String :=
  match t with
  | .cas .. => (s.drop 1).dropRight 1
  | _ => s

/-- `def name {ty_a …} (b : T) (a : T) : R := match b with …` for a generated function. -/
def exportFun (ds : List DatasH) (name : String) (tipo : Ty) (t : Term) : String :=
  let (ptys, res) := tipo.parsAndRet
  let k := ptys.length
  let vars := (sigParams ds tipo).eraseDups
  let implicit := vars.map fun v => s!" \{{paramName v} : Type}"
  let params := (ptys.zipIdx.map fun (ty, i) => s!" ({letter (k - 1 - i)} : {renderTy ds ty})")
  s!"def {name}{String.join implicit}{String.join params} : {renderTy ds res} :=\n  " ++
    (unparen (funBody t) (leanTerm ds name k ((List.range k).map letter) (funBody t))).replace "\n" "\n  " ++ "\n"

/-- A whole file: the data types, then the functions. -/
def exportFile (title : String) (ns : String) (ds : List DatasH) (funs : List (String × Ty × Term)) : String :=
  s!"-- {title}\n-- Generated by `lake exe export-lean`; do not edit by hand (the build, or `lake exe results`,\n" ++
  "-- checks that this file equals the generator's output).\n\n" ++
  s!"set_option linter.unusedVariables false\n\nnamespace {ns}\n\n" ++
  "\n".intercalate (ds.map (exportData ds)) ++ "\n" ++
  "\n".intercalate (funs.map fun (n, ty, t) => exportFun ds n ty t) ++ s!"\nend {ns}\n"

/-- The 64 first-search candidates (`Main.candidatosFst`), named `fstCand0 … fstCand63`. -/
def fstFile : String :=
  exportFile "The first-search candidates of foundations Main.candidatosFst, as plain Lean." "Gen"
    datas (candidatosFst.zipIdx.map fun ((t, ty), i) => (s!"fstCand{i}", ty, t))

end MM.Export
