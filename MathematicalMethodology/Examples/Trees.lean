import MathematicalMethodology.Strategic.FindLemmas
import MathematicalMethodology.Examples.TestEnv

/-!
# A development the exporter was not written against: polymorphic binary trees

Written for #59 as a generality test of the export (#53).  Nothing here comes from foundations'
`Test.hs` or Appendix B: a new data type `Tree` (leaves hold an element of the type variable
`a`, as `List` does), and three functions on it,

* `mirror`: swaps the subtrees everywhere;
* `size`: the number of leaves (uses `suma`);
* `flatten`: the leaves, left to right (uses `concat`).

`suma` and `concat` are taken from `Test.hs`.  The inputs (types, definitions, which symbols
each search may use) are written by hand, as foundations' `Test.hs` is; the lemmas and their
proofs are found by the system (`findlemas`), and `Export/Trees.lean` exports them.
-/

namespace MM.Examples.Trees

open MM MM.Strategic MM.Examples.TestEnv

def datas : List DatasH :=
  [ ("Nat", [("O", []), ("S", [(.con "Nat")])]),
    ("List", [("Nil", []), ("Cons", [(.var "a"), (.con "List")])]),
    ("Tree", [("Hoja", [(.var "a")]), ("Nodo", [(.con "Tree"), (.con "Tree")])]) ]

def app2 (f x y : Term) : Term := .app (.app f x) y

/-- `mirror (Hoja x) = Hoja x`, `mirror (Nodo l r) = Nodo (mirror r) (mirror l)`. -/
def mirrorDef : Term :=
  .abs (.cas (.var 0)
    (.alt "Hoja" 1 (.app (.con "Hoja") (.var 0))
    (.alt "Nodo" 2 (app2 (.con "Nodo") (.app (.const "mirror") (.var 0)) (.app (.const "mirror") (.var 1)))
    .nil)))

/-- `size (Hoja x) = S O`, `size (Nodo l r) = suma (size l) (size r)`. -/
def sizeDef : Term :=
  .abs (.cas (.var 0)
    (.alt "Hoja" 1 (.app (.con "S") (.con "O"))
    (.alt "Nodo" 2 (app2 (.const "suma") (.app (.const "size") (.var 1)) (.app (.const "size") (.var 0)))
    .nil)))

/-- `flatten (Hoja x) = Cons x Nil`, `flatten (Nodo l r) = concat (flatten l) (flatten r)`. -/
def flattenDef : Term :=
  .abs (.cas (.var 0)
    (.alt "Hoja" 1 (app2 (.con "Cons") (.var 0) (.con "Nil"))
    (.alt "Nodo" 2 (app2 (.const "concat") (.app (.const "flatten") (.var 1)) (.app (.const "flatten") (.var 0)))
    .nil)))

def pick (names : List String) : Env := env.filter fun (f, _) => names.contains f

/-- `suma`, `concat` (from `Test.hs`) and the three new functions, dependencies first. -/
def env' : Env :=
  pick ["suma", "concat", "rev"] ++
  [("mirror", mirrorDef), ("size", sizeDef), ("flatten", flattenDef)]

def tenv' : TEnv :=
  [ (Term.con "O", (.con "Nat")), (Term.con "S", (.com (.con "Nat") (.con "Nat"))),
    (Term.const "suma", (.com (.con "Nat") (.com (.con "Nat") (.con "Nat")))),
    (Term.con "Nil", (.con "List")),
    (Term.con "Cons", (.com (.con "a") (.com (.con "List") (.con "List")))),
    (Term.const "concat", (.com (.con "List") (.com (.con "List") (.con "List")))),
    (Term.const "rev", (.com (.con "List") (.con "List"))),
    (Term.con "Hoja", (.com (.con "a") (.con "Tree"))),
    (Term.con "Nodo", (.com (.con "Tree") (.com (.con "Tree") (.con "Tree")))),
    (Term.const "mirror", (.com (.con "Tree") (.con "Tree"))),
    (Term.const "size", (.com (.con "Tree") (.con "Nat"))),
    (Term.const "flatten", (.com (.con "Tree") (.con "List"))) ]

def sigs : List (String × Ty) :=
  tenv'.filterMap fun (t, ty) => match t with | .const f => some (f, ty) | _ => none

/-- The search context for the functions defined so far; the names the definitions use are
computed from the definitions (`defNamesOf`). -/
def ctxFor (e : Env) : PCtx :=
  mkPCtx e datas (e.flatMap fun (_, t) => defNamesOf t)

/-- The part of the vocabulary a search may use: the symbols with these names. -/
def vocab (names : List String) : TEnv :=
  tenv'.filter fun (t, _) => match t with
    | .con c | .const c => names.contains c
    | _ => false

/-- Lemmas for each function in turn, each search starting from the lemmas found before it
(`suma`, `concat`, `rev` first, as in `Test.hs`'s chains). -/
def chainData : List (String × List BatchResult) :=
  let find (n : Nat) (names : List String) (r : HRec) (f : String) :=
    findlemas (ctxFor (env'.take n)) (vocab names) 30 r f
  let upto (r : HRec) (ls : List BatchResult) := HRec.addAll env' r (lemmasOf ls)
  let lsuma := find 1 ["O", "S", "suma"] {} "suma"
  let r1 := upto {} lsuma
  let lconcat := find 2 ["Nil", "Cons", "concat"] r1 "concat"
  let r2 := upto r1 lconcat
  let lrev := find 3 ["Nil", "Cons", "concat", "rev"] r2 "rev"
  let r3 := upto r2 lrev
  let lmirror := find 4 ["Hoja", "Nodo", "mirror"] r3 "mirror"
  let r4 := upto r3 lmirror
  let lsize := find 5 ["O", "S", "suma", "Hoja", "Nodo", "mirror", "size"] r4 "size"
  let r5 := upto r4 lsize
  let lflat := find 6 ["Nil", "Cons", "concat", "rev", "Hoja", "Nodo", "mirror", "flatten"] r5 "flatten"
  [("suma", lsuma), ("concat", lconcat), ("rev", lrev), ("mirror", lmirror), ("size", lsize),
   ("flatten", lflat)]

def dump : String :=
  "\n".intercalate (chainData.flatMap fun (n, bs) =>
    s!"## {n}" :: (bs.filterMap (·.chosen)).filterMap (·.head.map fun h => s!"lemma {h.show}")) ++ "\n"

end MM.Examples.Trees
