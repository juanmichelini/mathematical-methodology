import MathematicalMethodology.Examples.Lists
import MathematicalMethodology.Tactical.Store

/-!
# Example: the lemma store on the list development

Expected values are worked out by hand from the Haskell definitions in
`juanmichelini/foundations` `code/Prove.hs` (GHC was not available to run them), see the
comments next to each check.
-/

namespace MM.Examples

open MM

def env := listCtx.env

/-! ## `fund` -/

-- append: abs (abs (cas ..)): 1 + 1 + (2 pattern variables + max body 1) = 5
#guard (Term.const "append").fund env = 5
-- rev: 1 + (2 + max(1, 6)) = 9, where the cons body is `append (rev t) (cons h nil)` = 5 + 1
#guard (Term.const "rev").fund env = 9

#guard (appendNil.lhs.fund env, appendNil.rhs.fund env) = (6, 0)
#guard (appendAssoc.lhs.fund env, appendAssoc.rhs.fund env) = (5, 5)
#guard (revAppend.lhs.fund env, revAppend.rhs.fund env) = (14, 9)
#guard (revRev.lhs.fund env, revRev.rhs.fund env) = (9, 0)

/-! ## Dependencies -/

#guard dependencies env (revT (.var 0)) =
  [.const "rev", .con "nil", .con "cons", .const "append", .var 0]

#guard compareDep env appendNil = some .gt
#guard simplifies env appendNil
#guard compareDep env appendAssoc = some .eq
#guard !simplifies env appendAssoc

/-! ## Orders -/

#guard ordEnv env (.const "append") (.const "rev") = .lt
#guard ordEnv env (.const "rev") (.var 0) = .gt
#guard ordEnv env (.var 0) (.var 1) = .eq
#guard floatsEnv env revAppend
-- the associativity lemma moves `append` towards the root: more dependencies on the left
#guard floatsDep env appendAssoc

#guard permuta appendAssoc
#guard !permuta appendNil
#guard toJera appendAssoc = some .reord
#guard toJera appendNil = some .swap

/-! ## Classification

`Rec.add` puts a lemma whose left side has the larger `fund` in `simp` (flipped if it is
the right side), a permutation lemma in `reor` (both directions), the rest in `basu`.
The `simp` list is sorted by the gap `fund lhs - fund rhs`: 5 (rev_append), 6 (append_nil),
9 (rev_rev). -/

def store : Rec := Rec.empty.addAll env [appendNil, appendAssoc, revAppend, revRev]

#guard store.simp == [revAppend, appendNil, revRev]
#guard store.reor == [appendAssoc, appendAssoc.flip]
#guard store.basu.isEmpty
#guard store.flod.isEmpty && store.floe.isEmpty && store.todo.isEmpty

-- A lemma given the wrong way round is stored flipped.
#guard (Rec.empty.add env appendNil.flip).simp == [appendNil]

/-! ## `masOrd` orients permutation lemmas -/

#guard masOrd appendAssoc.rhs appendAssoc.lhs = .lt
#guard masOrd appendAssoc.lhs appendAssoc.rhs = .gt
#guard masOrd appendAssoc.lhs appendAssoc.lhs = .eq

end MM.Examples
