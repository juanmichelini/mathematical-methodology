import MathematicalMethodology.Strategic.FindLemmas
import MathematicalMethodology.Strategic.FirstSearch
import MathematicalMethodology.Examples.TestEnv

/-!
# foundations `Test.hs`: the 35 lemmas and the lemma chains

* `Test.lemas`: 35 hand-written lemmas about booleans, naturals and lists, each proved with
  `lemascomp` and the lemmas before it as hypotheses (`Test.provelemas`), with the smallest
  search budget at which each is proved;
* the chains of `Test.hs`: lemmas found for `suma`; for `mult` with the lemmas of `suma`; for
  `flipexp` with those of `mult` (the two lemmas of thesis Sec. 10: `c^(a+b) = c^a * c^b` and
  `c^(a*b) = (c^b)^a`); for `min`, `max`, `absr`, `and`, `or`, `not`, `concat`, and `rev`
  with the lemmas of `concat`.

The definitions and the lemmas are generated from the Haskell (`Examples/TestEnv.lean`).
Ground truth: `scripts/haskell/TestSuite.hs` (`fixtures/haskell/test_suite.txt`).
-/

namespace MM.Examples.TestSuite

open MM MM.Strategic MM.Examples.TestEnv

/-- Names used by the definitions of an environment (Haskell `usedVars`). -/
def usedBy (env : Env) : List String :=
  (env.flatMap fun (f, _) => (defUsed.lookup f).getD []).eraseDups

def ctxFor (env : Env) : PCtx :=
  { env := env, data := dataDecls TestEnv.datas, defNames := usedBy env }

/-- Smallest budget in `1..60` at which `c` is proved from `rec`. -/
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

/-- `provelemas 30`: lemma `n` is proved with `lemascomp ++ take n lemas` as hypotheses. -/
def lemmaLines : List String :=
  let cx := ctxFor env
  lemas.zipIdx.map fun (l, n) =>
    let rec_ := HRec.addAll env {} (lemascomp ++ lemas.take n)
    let ok := (prove cx 30 rec_ l).complete
    let nd := match need cx rec_ l with | some k => toString k | none => "fail"
    (if ok then "OK   " else "fail ") ++ nd ++ " " ++ l.show

def chainLines (name : String) (bs : List BatchResult) : List String :=
  let ps := bs.filterMap (·.chosen)
  s!"## {name}" :: ps.filterMap (·.head.map fun h => s!"lemma {h.show}") ++
    [s!"done {(ps.map Proof.doneCount).foldl (· + ·) 0}"]

/-- Lemmas of the proofs found, as statements. -/
def lemmasOfBatches (bs : List BatchResult) : List Conj := lemmasOf bs

/-- The chains of `Test.hs`: for each function, the batches `findlemas` produced, in order. -/
def chainData : List (String × List BatchResult) :=
  let find (e : Env) (t : TEnv) (rec_ : HRec) (f : String) := findlemas (ctxFor e) t 30 rec_ f
  let lsuma := find (env.take 3) (tenv.take 5) {} "suma"
  let lsumar := HRec.addAll env {} (lemmasOf lsuma)
  let lmult := find (env.take 4) (tenv.take 6) lsumar "mult"
  let lmultr := HRec.addAll env lsumar (lemmasOf lmult)
  let lexp := find (env.take 5) (tenv.take 6) lmultr "flipexp"
  let lconcat := find env tenv {} "concat"
  let lconcatr := HRec.addAll env {} (lemmasOf lconcat)
  [("suma", lsuma), ("mult", lmult), ("flipexp", lexp),
   ("min", find env tenv {} "min"), ("max", find env tenv {} "max"),
   ("absr", find env tenv {} "absr"), ("and", find env tenv {} "and"),
   ("or", find env tenv {} "or"), ("not", find env tenv {} "not"),
   ("concat", lconcat), ("rev", find env tenv lconcatr "rev")]

def chains : List String :=
  chainData.flatMap fun (n, bs) => chainLines n bs

/-- `provelemas 30`: the proof of each of the 35 lemmas, from `lemascomp` and the lemmas before it. -/
def lemmaProofs : List Proof :=
  let cx := ctxFor env
  lemas.zipIdx.map fun (l, n) => prove cx 30 (HRec.addAll env {} (lemascomp ++ lemas.take n)) l

/-- The proofs of the five `lemascomp` lemmas (each from those before it). -/
def compProofs : List Proof :=
  let cx := ctxFor env
  lemascomp.zipIdx.map fun (l, n) => prove cx 30 (HRec.addAll env {} (lemascomp.take n)) l

def dump : String :=
  "\n".intercalate (s!"## lemas {lemas.length}" :: lemmaLines ++ chains) ++ "\n"

end MM.Examples.TestSuite
