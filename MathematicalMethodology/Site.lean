import Lean.Data.Json
import MathematicalMethodology.Export.Suite
import MathematicalMethodology.Examples.FirstSearch
import MathematicalMethodology.Examples.SecondSearch

/-!
# Data for the website

`lake exe site-data > results/site-data.json` writes everything the website shows about the
results as JSON: for Appendix B, the `Test.hs` suite and the tree development, the definitions,
every lemma with the proof the system found **in the thesis' format** (`{ Compute }`,
`{ Fund: lemma }`, `{ Induction on x }`, `T)` / `H)` for the cases of an induction), and the name
of the Lean theorem the lemma was exported to (the numbering is `Export.nameProofs`, the one the
export uses, so `Generated/*.lean` can be paired by name).

Display only; **untrusted**; nothing trusted imports it.  Deterministic, committed, and checked up
to date by CI like `results/report.md`.
-/

namespace MM.Site

open Lean MM MM.Strategic MM.Export

/-! ## A proof in the thesis' format -/

/-- One line of a proof: its kind (`goal`, `step`, `case`, `hyp`, `done`, `fail`), its text and
the nesting depth (inside the cases of an induction). -/
structure Line where
  kind : String
  text : String
  depth : Nat

def Line.json (l : Line) : Json :=
  Json.mkObj [("k", l.kind), ("t", l.text), ("d", l.depth)]

/-- `lhs = rhs` with the variable names of the conjecture. -/
def equation (c : Conj) : String :=
  showNamed c.names c.aff.lhs ++ " = " ++ showNamed c.names c.aff.rhs

def sideText : SideComment → String
  | .compute => "Compute"
  | .lemma _ l _ => s!"Fund: {equation l}"

def commentText : Comment → String
  | .noIdea => "No idea"
  | .triv => "Triv"
  | .loop => "Loop"
  | .left s => sideText s
  | .right s => sideText s
  | .both s t => sideText s ++ " ; " ++ sideText t
  | .induction v => s!"Induction on {v}"
  | .caso v c fs _ => s!"Case {v} = {" ".intercalate (c :: fs)}"

mutual
  def proofLines (d : Nat) : Proof → List Line
    | .done => [⟨"done", "Done.", d⟩]
    | .fail => [⟨"fail", "Failed.", d⟩]
    | .step a cm p => ⟨"goal", equation a, d⟩ :: ⟨"step", commentText cm, d⟩ :: proofLines d p
    | .ind a cm cs => ⟨"goal", equation a, d⟩ :: ⟨"step", commentText cm, d⟩ :: caseLines d cs

  def caseLines (d : Nat) : List (Comment × List Conj × Proof) → List Line
    | [] => []
    | (cm, hs, p) :: rest =>
      ⟨"case", commentText cm, d + 1⟩ :: (hs.map fun h => ⟨"hyp", equation h, d + 1⟩) ++
        proofLines (d + 1) p ++ caseLines d rest
end

/-! ## Developments -/

/-- A lemma with its proof, the Lean theorem it was exported to (none if the system did not
prove it: the Haskell takes it as given) and the statement. -/
def lemmaJson (id : Option String) (p : Proof) : Json :=
  let stmt := (p.head.map fun c => c.show).getD ""
  Json.mkObj [
    ("id", match id with | some i => Json.str i | none => Json.null),
    ("statement", stmt),
    ("proved", p.complete),
    ("done", p.doneCount),
    ("proof", Json.arr ((proofLines 0 p).map Line.json).toArray)]

/-- The proofs of a group in order; the complete ones carry the name of their theorem. -/
def groupLemmas (g : String) (ps : List Proof) : List Json :=
  let named := nameProofs g ps
  let rec go (ps : List Proof) (named : List (String × Proof)) : List Json :=
    match ps with
    | [] => []
    | p :: rest =>
      if p.complete then
        match named with
        | (n, _) :: more => lemmaJson (some n) p :: go rest more
        | [] => lemmaJson none p :: go rest []
      else lemmaJson none p :: go rest named
  go ps named

def funJson (name definition ty : String) (lemmas : List Json) : Json :=
  Json.mkObj [("name", name), ("definition", definition), ("type", ty),
    ("lemmas", Json.arr lemmas.toArray)]

def appendixB : Json :=
  let sel := MM.Examples.FirstSearch.selected ++ MM.Examples.SecondSearch.selected
  Json.arr (sel.map (fun s =>
    funJson s.name (showFunN s.params s.fields s.name s.def_) s.ty.pp
      (groupLemmas s.name s.proofs)) |>.toArray)

/-- A development: its functions (thesis notation, type) and the groups of lemmas. -/
def development (funs : List (String × Ty × Term)) (groups : List (String × List Proof)) : Json :=
  Json.mkObj [
    ("functions", Json.arr (funs.map (fun (n, ty, t) =>
      Json.mkObj [("name", n), ("definition", showFun t), ("type", ty.pp)]) |>.toArray)),
    ("groups", Json.arr (groups.map (fun (g, ps) =>
      Json.mkObj [("name", g), ("lemmas", Json.arr (groupLemmas g ps).toArray)]) |>.toArray))]

def siteData : Json :=
  Json.mkObj [
    ("about", "Written by `lake exe site-data`; do not edit by hand (CI checks it is up to date)."),
    ("appendixB", appendixB),
    ("suite", development suiteFuns suiteGroups),
    ("trees", development treesFuns treesGroups)]

end MM.Site
