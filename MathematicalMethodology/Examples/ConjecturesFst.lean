import MathematicalMethodology.Strategic.Conjecture

/-!
# Conjectures for the first-search candidates, against the Haskell

Ground truth: foundations `plemas` run on GHC for each of the 64 first-search candidates
(`fixtures/haskell/conj_fst.txt`, 8222 lines; see `docs/DEVELOPMENT.md`).  The guard checks
that the Lean conjectures are the same, statement by statement and in the same order, with
the same variable names.
-/

namespace MM.Examples.ConjecturesFst

open MM MM.Strategic

/-- The Haskell dump format: for each candidate, each batch, each conjecture. -/
def dump : String :=
  let blocks := candidatosFst.zipIdx.map fun ((f, ty), i) =>
    let tenv : TEnv := (Term.const "f", ty) :: cerothTEnv
    let batches := plemas noReject [("f", f)] tenv "f"
    let body := batches.zipIdx.flatMap fun (b, j) => s!"# batch {j}" :: b.map Conj.show
    "\n".intercalate (s!"## cand {i}" :: body)
  "\n".intercalate blocks ++ "\n"

-- the 8222 lines the original Haskell prints (statements, names, order)
#guard dump == include_str "../../fixtures/haskell/conj_fst.txt"

end MM.Examples.ConjecturesFst
