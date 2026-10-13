import MathematicalMethodology.Strategic.Enumerate

/-!
# Enumeration: tests

The data types and the first-search candidates of foundations `Main.hs`.  All checks are
`#guard`s, so a successful `lake build` means they hold.  The counts come from foundations
`results/experiments.txt` (first search: 64 candidates).  The 164 candidates of the second
search depend on the output of the first search (`fstEnv`), so they are checked with the
second search (issue #27).
-/

namespace MM.Examples.Enumeration

open MM.Strategic

/-! ## Helpers -/

#guard hilar [[1, 2], [3, 4]] = [[1, 3], [2, 3], [1, 4], [2, 4]]
#guard hilar ([] : List (List Nat)) = [[]]
#guard hilar [[1], []] = []
#guard dist 2 [1, 2] = [[[], [1, 2]], [[1], [2]], [[1, 2], []]]
#guard dist 3 ([] : List Nat) = [[[], [], []]]
#guard dist 1 [1, 2] = [[[1, 2]]]
#guard dist 0 [1, 2] = []

/-! ## Data types -/

-- `Main.datas`: Bool-, Nat-, Maybe- and List-shaped types, in this order.
#guard datas.map (·.1) = ["C_,_", "C_,R", "C_,a", "C_,a_R"]
#guard datas.map (fun d => d.2.map fun (c, fs) => (c, fs.map Ty.pp)) =
  [ [("C_,_.0", []), ("C_,_.1", [])]
  , [("C_,R.0", []), ("C_,R.1", ["C_,R"])]
  , [("C_,a.0", []), ("C_,a.1", ["a"])]
  , [("C_,a_R.0", []), ("C_,a_R.1", ["a", "C_,a_R"])] ]

#guard (enumSimpleFiniteTypes 2) = ("F2", [("F2.1", []), ("F2.2", [])])
#guard (enumContainerFiniteTypes 2 1).map (·.1) = ["C_,a", "Ca,_"]
#guard (enumRecursiveTypes 2 1).map (·.1) = ["C_,rec", "Crec,_"]
-- no constructors fit in zero blocks
#guard (enumContainerRecTypes 0 1 1).isEmpty

-- Constructor types: `S : Nat → Nat`.
#guard (datas[1]!).toC.map (fun (c, t) => (c, t.pp)) =
  [("C_,R.0", "C_,R"), ("C_,R.1", "(C_,R -> C_,R)")]

/-! ## Function types and parameters -/

#guard (armarTip 1 [.con "N", .con "L"]).map Ty.pp =
  ["(N -> N)", "(N -> L)", "(L -> N)", "(L -> L)"]
#guard (armarTip 2 [.con "N", .con "L"]).length = 8
#guard armarPar (.com (.con "N") (.com (.con "N") (.con "N"))) =
  [("b", .con "N"), ("a", .con "N")]

/-! ## Expressions -/

private def natEnv : TEnv :=
  [(NTerm.con "O", .con "N"), (NTerm.con "S", .com (.con "N") (.con "N"))]

#guard (enumApp 0 (.con "N") natEnv).map NTerm.pp = ["O"]
#guard (enumApp 1 (.con "N") natEnv).map NTerm.pp = ["O", "(S O)"]
#guard (enumApp 2 (.con "N") natEnv).map NTerm.pp = ["O", "(S O)", "(S (S O))"]
-- nothing of an unknown type
#guard (enumApp 3 (.con "Z") natEnv).isEmpty

-- the recursion filter drops terms
#guard (enumAppRec (fun t => t.contains (.con "S")) 2 (.con "N") natEnv).map NTerm.pp = ["O"]

-- an atom may occur at most twice
#guard (repiteAtmHasta 3 [(NTerm.var "x").app ((NTerm.var "x").app (NTerm.var "x")),
    (NTerm.var "x").app (NTerm.var "y")]).length = 1

/-! ## Functions -/

-- the type of the function must start with a declared data type
#guard (enumFun (fun _ => false) "f" (.com (.con "Z") (.con "Z")) datas cerothTEnv).isEmpty
#guard (enumFun (fun _ => false) "f" (.con "C_,R") datas cerothTEnv).isEmpty

-- `suma` is among the candidates `Nat → Nat → Nat`
#guard (candidatosFst.map fun (e, _) => e.pp).contains
  "(\\b -> (\\a -> (case b of {C_,R.0 -> a; C_,R.1 c -> (C_,R.1 ((f c) a))})))"

/-! ## First-search candidates -/

-- foundations `results/experiments.txt`: "first search candidates: 64"
#guard candidatosFst.length = 64
-- every candidate mentions its own name (recursion)
#guard candidatosFst.all fun (e, _) => e.contains (.var "f")

end MM.Examples.Enumeration
