import MathematicalMethodology.Strategic.Enumerate
import MathematicalMethodology.Strategic.Show
import MathematicalMethodology.Examples.HaskellFst

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

/-! ## Function types -/

#guard (armarTip 1 [.con "N", .con "L"]).map Ty.pp =
  ["(N -> N)", "(N -> L)", "(L -> N)", "(L -> L)"]
#guard (armarTip 2 [.con "N", .con "L"]).length = 8

/-! ## Expressions -/

private def natEnv : TEnv :=
  [(Term.con "O", .con "N"), (Term.con "S", .com (.con "N") (.con "N"))]

private def ppT : Term → String := showTerm 0 0

#guard (enumApp 0 (.con "N") natEnv).map ppT = ["O"]
#guard (enumApp 1 (.con "N") natEnv).map ppT = ["O", "S O"]
#guard (enumApp 2 (.con "N") natEnv).map ppT = ["O", "S O", "S (S O)"]
-- nothing of an unknown type
#guard (enumApp 3 (.con "Z") natEnv).isEmpty

-- the recursion filter drops terms
#guard (enumAppRec (fun t => (termAtoms 0 0 t).contains (.con "S")) 2 (.con "N") natEnv).map ppT
  = ["O"]

/-! ## Counting atoms (`repiteAtmHasta`)

Parameters and fields are counted by position from the left, so a field of one constructor
and the same-position field of another are the same atom, whatever their de Bruijn index. -/

-- inside an alternative of arity 2 under 1 parameter: var 1 = field 0, var 0 = field 1,
-- var 2 = parameter 0
#guard termAtoms 1 2 (.app (.var 1) (.app (.var 0) (.var 2))) =
  [.field 0, .field 1, .param 0]
-- the same fields in an alternative of arity 3: other indices, same atoms
#guard termAtoms 1 3 (.app (.var 2) (.app (.var 1) (.var 3))) =
  [.field 0, .field 1, .param 0]
-- two parameters: the first is the outer one
#guard termAtoms 2 0 (.app (.var 1) (.var 0)) = [.param 0, .param 1]

-- field 0 of an arity-2 alternative and field 0 of an arity-1 alternative are one atom,
-- although their indices differ (`var 1` and `var 0`): three occurrences are too many
private def twoAlts (b0 b1 : Term) : Term :=
  .cas (.var 0) (.alt "A" 2 b0 (.alt "B" 1 b1 .nil))

#guard (repiteAtmHasta 1 3 [twoAlts (.app (.var 1) (.var 1)) (.var 0)]).isEmpty
-- fields 1 (of A) and 0 (of B) are different atoms: two occurrences each is fine
#guard (repiteAtmHasta 1 3 [twoAlts (.app (.var 0) (.var 0)) (.app (.var 0) (.var 0))]).length = 1

/-! ## Functions -/

-- the type of the function must start with a declared data type
#guard (enumFun (fun _ => false) "f" (.com (.con "Z") (.con "Z")) datas cerothTEnv).isEmpty
#guard (enumFun (fun _ => false) "f" (.con "C_,R") datas cerothTEnv).isEmpty

-- `suma` is among the candidates `Nat → Nat → Nat`
#guard (candidatosFst.map fun (e, _) => showFun e).contains
  "\\b -> \\a -> case b of { C_,R.0 -> a; C_,R.1 c -> C_,R.1 (f c a); }"

/-! ## First-search candidates -/

-- foundations `results/experiments.txt`: "first search candidates: 64"
#guard candidatosFst.length = 64
-- every candidate mentions its own name (recursion)
#guard candidatosFst.all fun (e, _) => mentions "f" e

/-- Candidates as `term  ::  type`, in the format of `haskellFst`. -/
def fstLines : List String :=
  candidatosFst.map fun (e, t) => showFun e ++ "  ::  " ++ t.pp

-- the full list, in order, equals what the original Haskell prints
#guard fstLines = haskellFst

end MM.Examples.Enumeration
