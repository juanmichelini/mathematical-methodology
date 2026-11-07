import MathematicalMethodology.Export.Lean
import MathematicalMethodology.Strategic.SecondSearch

/-!
# Export of proofs as Lean theorems

Prints the lemmas found by the search (`Strategic/FirstSearch.lean`, `SecondSearch.lean`) as
Lean `theorem`s about the exported functions (`Export/AppendixB.lean`), with the proof the
search found, so that **Lean's kernel re-checks them independently of this project**.
`Cert.check_sound` is about our own `Conv`, not Lean's `=`; this export is the bridge,
validated by compilation.

Mapping of the steps of a `Proof` (Haskell's) to tactics:

| step | tactic |
|---|---|
| `Triv` | `try rfl` (a `conv` rewrite already closes goals that become syntactically equal) |
| `Compute` (definitional unfolding and reduction) | `change <next statement>` |
| rewrite with a lemma / hypothesis, left or right side | `try (conv => lhs; rw [lemma args])` / `… rhs …` (`←` for a flipped lemma; core Lean, no Mathlib). Haskell rewrites one occurrence per step, Lean's `rw` all identical ones, so a repeated step may find nothing: `try`. A missing rewrite cannot make a wrong proof pass: the kernel checks the whole theorem. |
| induction on the first variable, hypothesis quantified over the other variables | `induction x generalizing y z with | C k ih_k => …` |

That is exactly Haskell's hypothesis: universally quantified over the remaining variables.
Steps that have no mapping are written as `sorry` and counted (`Unmapped`).  **Untrusted.**
-/

namespace MM.Export

open MM MM.Strategic

/-! ## Statements -/

/-- Constructors with parameters that take no arguments need a type ascription. -/
def nullaryParam (ds : List DatasH) (c : String) : Option String :=
  match ds.find? fun d => d.2.any (·.1 == c) with
  | some d =>
    let isNullary := (d.2.find? (·.1 == c)).any (·.2.isEmpty)
    if isNullary && !(dataParams d).isEmpty then
      some (String.intercalate " " (sanitize d.1 :: (dataParams d).map paramName))
    else none
  | none => none

/-- A term of a statement in Lean syntax: variable `i` is `names[i]`; the opaque constants the
induction introduces are the pattern variables of the same name. -/
def leanOpen (ds : List DatasH) (names : List String) : Term → String
  | .var i => names.getD i s!"_v{i}"
  | .con c =>
    match nullaryParam ds c with
    | some ty => s!"({ctorName ds c} : {ty})"
    | none => ctorName ds c
  | .const f => sanitize f
  | .app x (.app y z) => leanOpen ds names x ++ " (" ++ leanOpen ds names (.app y z) ++ ")"
  | .app x y => leanOpen ds names x ++ " " ++ leanOpen ds names y
  | _ => "_"

/-- A variable's type, from the printed type of the context. -/
def renderCtxTy (ds : List DatasH) (t : String) : String :=
  if ds.any (·.1 == t) then renderTy ds (.con t) else paramName t

def ctxParams (ds : List DatasH) (t : String) : List String :=
  match ds.find? (·.1 == t) with
  | some d => dataParams d
  | none => [t]

/-- Type parameters of the nullary constructors that get an ascription in a term. -/
def termParams (ds : List DatasH) : Term → List String
  | .con c =>
    match ds.find? fun d => d.2.any (·.1 == c) with
    | some d => if (nullaryParam ds c).isSome then dataParams d else []
    | none => []
  | .app f a => termParams ds f ++ termParams ds a
  | _ => []

def theoremHeader (ds : List DatasH) (name : String) (c : Conj) : String :=
  let ps := (c.aff.ctx.flatMap (ctxParams ds) ++ termParams ds c.aff.lhs ++
    termParams ds c.aff.rhs).eraseDups
  let implicit := ps.map fun p => s!" \{{paramName p} : Type}"
  let binders := (c.names.zip c.aff.ctx).map fun (n, t) => s!" ({n} : {renderCtxTy ds t})"
  s!"theorem {name}{String.join implicit}{String.join binders} :\n    " ++
    leanOpen ds c.names c.aff.lhs ++ " = " ++ leanOpen ds c.names c.aff.rhs ++ " := by"

/-! ## Proofs -/

/-- A lemma or hypothesis available in a proof. -/
structure Avail where
  name : String
  stmt : Conj

/-- The theorem (and whether it is used right to left) for a stored lemma. -/
def findAvail (avail : List Avail) (l : Conj) : Option (String × Bool) :=
  match avail.find? (·.stmt == l) with
  | some a => some (a.name, false)
  | none => (avail.find? (·.stmt == l.flip)).map fun a => (a.name, true)

/-- The arguments of a lemma, in the order of its variables, from the binding. -/
def lemmaArgs (ds : List DatasH) (goalNames : List String) (nvars : Nat) (b : List (Nat × Term)) :
    String :=
  String.join ((List.range nvars).map fun i =>
    match b.find? (·.1 == i) with
    | some (_, t) =>
      let s := leanOpen ds goalNames t
      match t with
      | .app .. => s!" ({s})"
      | _ => s!" {s}"
    | none => " _")

/-- Number of steps that have no tactic. -/
structure Counters where
  unmapped : Nat := 0
  deriving Repr

mutual
  /-- Tactics for a proof, one per line, indented by `ind`. -/
  def proofLines (ds : List DatasH) (avail : List Avail) (ind : String) : Proof → List String
    | .done => []
    | .fail => [ind ++ "sorry -- unmapped: failed proof"]
    | .step c cm rest =>
      let sideRw (side : String) (s : SideComment) : List String :=
        match s with
        | .compute => []
        | .lemma _ l b =>
          match findAvail avail l with
          | some (nm, flipped) =>
            let arrow := if flipped then "← " else ""
            [ind ++ s!"try (conv => {side}; rw [{arrow}{nm}{lemmaArgs ds c.names l.aff.ctx.length b}])"]
          | none => [ind ++ s!"sorry -- unmapped: lemma {l.show}"]
      let next : List String := match rest.head with
        | some n => [ind ++ s!"change {leanOpen ds n.names n.aff.lhs} = {leanOpen ds n.names n.aff.rhs}"]
        | none => []
      let here : List String :=
        match cm with
        | .triv => [ind ++ "try rfl"]
        | .noIdea => [ind ++ "sorry -- unmapped: no idea"]
        | .loop => [ind ++ "sorry -- unmapped: loop"]
        | .induction _ => [ind ++ "sorry -- unmapped"]
        | .caso .. => [ind ++ "sorry -- unmapped"]
        | .left (.lemma r l b) => sideRw "lhs" (.lemma r l b)
        | .right (.lemma r l b) => sideRw "rhs" (.lemma r l b)
        | .both (.lemma r l b) (.lemma r' l' b') => sideRw "lhs" (.lemma r l b) ++ sideRw "rhs" (.lemma r' l' b')
        | .left .compute | .right .compute | .both .compute .compute => next
        | _ => [ind ++ "sorry -- unmapped: mixed step"]
      here ++ proofLines ds avail ind rest
    | .ind c _ cases =>
      let v := c.names.headD "_"
      let others := c.names.drop 1
      let gen := if others.isEmpty then "" else " generalizing " ++ " ".intercalate others
      [ind ++ s!"induction {v}{gen} with"] ++ caseLines ds avail ind cases

  def caseLines (ds : List DatasH) (avail : List Avail) (ind : String) :
      List (Comment × List Conj × Proof) → List String
    | [] => []
    | (cm, hs, p) :: rest =>
      let hdr := match cm with
        | .caso _ con fields recs =>
          ind ++ s!"| {sanitize con}" ++ String.join (fields.map (" " ++ ·)) ++
            String.join (recs.map fun r => s!" ih_{r}") ++ " =>"
        | _ => ind ++ "| _ =>"
      let ihs : List Avail := match cm with
        | .caso _ _ _ recs => (recs.zip hs).map fun (r, h) => ⟨s!"ih_{r}", h⟩
        | _ => []
      [hdr] ++ proofLines ds (ihs ++ avail) (ind ++ "  ") p ++ caseLines ds avail ind rest
end

/-- Number of `sorry`s in the generated lines. -/
def countUnmapped (ls : List String) : Nat :=
  (ls.filter fun (l : String) => (l.splitOn "sorry").length > 1).length

/-- A theorem for a lemma and its proof. -/
def exportTheorem (ds : List DatasH) (avail : List Avail) (name : String) (c : Conj) (p : Proof) :
    String :=
  "\n".intercalate (theoremHeader ds name c :: proofLines ds avail "  " p) ++ "\n"

/-- The proofs of a group that become theorems, with their names: the complete ones, in order;
theorem `i` of group `g` is called `g_l{i+1}`.  One place for the numbering, shared by the
export and by the site data (`Site.lean`). -/
def nameProofs (g : String) (ps : List Proof) : List (String × Proof) :=
  ((ps.filter Proof.complete).zipIdx).map fun (p, i) => (s!"{sanitize g}_l{i + 1}", p)

/-- Theorems for groups of proofs, in order; each can use every earlier theorem.  A group is a
name prefix and the proofs found for it.  Returns the theorems, the lemma-to-name list, and the
number of steps with no tactic. -/
def theoremsFor (ds : List DatasH) (initial : List Avail) (groups : List (String × List Proof)) :
    List String × List Avail × Nat :=
  groups.foldl
    (fun (acc : List String × List Avail × Nat) (g, proofs) =>
      (nameProofs g proofs).foldl
        (fun (acc : List String × List Avail × Nat) (name, p) =>
          let (texts, av, bad) := acc
          match p.head with
          | none => acc
          | some c =>
            (texts ++ [exportTheorem ds av name c p], av ++ [⟨name, c⟩],
              bad + countUnmapped (proofLines ds av "  " p)))
        acc)
    ([], initial, 0)

/-- The theorems of all selected functions, in order; each can use every earlier lemma. -/
def proofsOf (ds : List DatasH) (sel : List Selected) : List String × Nat :=
  let (ts, _, bad) := theoremsFor ds [] (sel.map fun s => (s.name, s.proofs))
  (ts, bad)

def proofsFile (sel : List Selected) : String × Nat :=
  let (ts, bad) := proofsOf datas sel
  ("-- The lemmas found for f0..f30 (Appendix B) as Lean theorems, with the proofs the search\n" ++
   "-- found.  Generated by `lake exe export-lean proofs`; do not edit by hand.\n\n" ++
   "import MathematicalMethodology.Generated.AppendixB\n\n" ++
   "set_option linter.unusedVariables false\n\nnamespace AppB\n\n" ++
   "\n".intercalate ts ++ "\nend AppB\n", bad)

end MM.Export
