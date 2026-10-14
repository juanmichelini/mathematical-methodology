import MathematicalMethodology.Strategic.Conjecture
import MathematicalMethodology.Examples.TestEnv

/-!
# Conjectures for the functions of foundations `Test.hs`, against the Haskell

`plemas` for every function of `Test.env` that has a type in `Test.tenv` (empty rule store),
and `pfindlemasAll` (`ampleAll` + `conjeturasAll`) for `suma, mult` and `concat, rev`.
Ground truth: the Haskell run on GHC (`fixtures/haskell/conj_test.txt`,
`scripts/haskell/TestConj.hs`).  The definitions themselves are generated from the Haskell
(`Examples/TestEnv.lean`).
-/

namespace MM.Examples.ConjecturesTest

open MM MM.Strategic MM.Examples.TestEnv

def fns : List String :=
  ["suma", "mult", "flipexp", "not", "and", "or", "ssi", "xor", "mayoria", "par", "doble",
   "pred", "min", "max", "absr", "concat", "largo", "rev"]

def inTenv (f : String) : Bool := (tenv.find? (·.1 == .const f)).isSome

/-- Same text as `scripts/haskell/TestConj.hs`. -/
def dump : String :=
  let perFn := (fns.filter inTenv).map fun f =>
    let batches := plemas noReject env tenv f
    "\n".intercalate (s!"## fn {f}" :: batches.zipIdx.flatMap fun (b, j) =>
      s!"# batch {j}" :: b.map Conj.show)
  let all (vs : List String) : String :=
    "\n".intercalate (s!"## all {" ".intercalate vs}" ::
      ((ampleAll tenv vs).flatMap (conjeturasAll noReject tenv)).map Conj.show)
  "\n".intercalate (perFn ++ [all ["suma", "mult"], all ["concat", "rev"]]) ++ "\n"

end MM.Examples.ConjecturesTest
