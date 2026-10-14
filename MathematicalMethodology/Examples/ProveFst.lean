import MathematicalMethodology.Strategic.FindLemmas
import MathematicalMethodology.Strategic.Show

/-!
# The proof search on the first-search candidates, against the Haskell

For every conjecture that `provell` actually tries, Haskell's `prove` is run at the smallest
budget at which it completes (`ProveTrace.hs`, `fixtures/haskell/prove_fst.txt`).  The
Lean trace must be the same line by line: same conjectures tried, same ones proven, same
smallest budget, same lemma chosen from each batch.
-/

namespace MM.Examples.ProveFst

open MM MM.Strategic

/-- Smallest budget in `1..60` at which the proof completes (monotone, so bisect). -/
def need (cx : PCtx) (rec : HRec) (c : Conj) : Option Nat :=
  let ok (n : Nat) := (prove cx n rec c).complete
  if !ok 60 then none else
  Id.run do
    let mut lo := 1
    let mut hi := 60
    while lo < hi do
      let mid := (lo + hi) / 2
      if ok mid then hi := mid else lo := mid + 1
    return some lo

/-- `provell` with the same text output as the Haskell trace. -/
def traceCand (cx : PCtx) (n : Nat) (rec : HRec) (bs : List (List Conj)) : List String :=
  match bs with
  | [] => []
  | b :: rest =>
    let cands := b.filter fun c => (applyRecH rec c).isNone
    let tried := cands.map fun c => (c, prove cx n rec c)
    let lines := tried.map fun (c, p) =>
      let nd := match need cx rec c with | some k => toString k | none => "fail"
      (if p.complete then "  OK   " else "  fail ") ++ nd ++ " " ++ c.show
    match tried.find? (·.2.complete) with
    | none => lines ++ ["# none"] ++ traceCand cx n rec rest
    | some (_, p) =>
      match p.head with
      | none => lines ++ traceCand cx n rec rest
      | some h =>
        lines ++ [s!"# chose {h.show}"] ++ traceCand cx n (rec.addAll cx.env [h]) rest

def dump : String :=
  let blocks := candidatosFst.zipIdx.map fun ((f, ty), i) =>
    let tenv : TEnv := (Term.const "f", ty) :: cerothTEnv
    let cx := mkPCtx [("f", f)] datas (defNamesOf f)
    let bs := plemas (rejectWith {}) cx.env tenv "f"
    let ls := traceCand cx 30 {} bs
    let k := (ls.filter (·.startsWith "# chose")).length
    "\n".intercalate (s!"## cand {i}" :: ls ++ [s!"# lemmas {k}"])
  "\n".intercalate blocks ++ "\n"

/-- Foundations' first search for a given `paciencia`: the candidates that keep more than three
lemmas, with the lemmas they keep (`Main.candidatosFstSel`). -/
def firstSearch (n : Nat) : List (Nat × List Conj) :=
  candidatosFst.zipIdx.filterMap fun ((f, ty), i) =>
    let tenv : TEnv := (Term.const "f", ty) :: cerothTEnv
    let cx := mkPCtx [("f", f)] datas (defNamesOf f)
    let ls := lemmasOf (findlemas cx tenv n {} "f")
    if ls.length > 3 then some (i, ls) else none

/-- From foundations `results/experiments.txt` ("First search vs paciencia"): for each
`paciencia`, the number of lemmas of each kept function. -/
def haskellCounts : List (Nat × List Nat) :=
  [(5, []), (10, [4, 4, 4]), (20, [7, 7, 4]), (30, [7, 7, 4]), (40, [7, 7, 4])]

def counts (n : Nat) : List Nat := (firstSearch n).map (·.2.length)

-- every conjecture tried, every proof found, the budget each needs, every lemma chosen:
-- the Haskell's trace
#guard dump == include_str "../../fixtures/haskell/prove_fst.txt"

/-- For each kept function (at `paciencia` 30): lemmas found, and how many of them the
checker-based search (`Tactical/Search.lean`) certifies and `Cert.check` accepts. -/
def certified : List (Nat × Nat × Nat) :=
  (firstSearch 30).map fun (i, ls) =>
    let (f, ty) := (candidatosFst[i]?).getD (Term.var 0, Ty.con "?")
    let tenv : TEnv := (Term.const "f", ty) :: cerothTEnv
    let cx := mkCtx [("f", f)] datas tenv
    (i, ls.length, ((certify cx 40 [] ls).filter id).length)

-- foundations' table (the report checks all five `paciencia` values)
#guard counts 10 == [4, 4, 4]
#guard counts 30 == [7, 7, 4]

end MM.Examples.ProveFst
