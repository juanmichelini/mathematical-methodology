import MathematicalMethodology.Strategic.FirstSearch

/-!
# The first search, against the Haskell

Foundations `Main.namedFstSel` and `Main.fstRec`, printed by `scripts/haskell/FstSel.hs`
(`fixtures/haskell/fst_sel.txt`): for each kept function the definition (with the binder
names Haskell gives it), type, the variable names it uses, its lemmas and the number of
finished proofs; then the lemma store in order.
-/

namespace MM.Examples.FirstSearch

open MM MM.Strategic

def selected : List Selected := selectFirst 30

def dump : String :=
  let fns := selected.map Selected.dump
  let r := fstRec selected
  let store := ["## fstRec"] ++ r.simp.map (fun l => s!"simp {l.show}") ++
    r.reor.map (fun l => s!"reor {l.show}") ++ r.basu.map (fun l => s!"basu {l.show}")
  "\n".intercalate (fns ++ [ "\n".intercalate store ]) ++ "\n"

#guard dump == include_str "../../fixtures/haskell/fst_sel.txt"

/-- From foundations `results/appendixB_comparison.md`: lemmas and finished proofs of f0-f2. -/
def appendixB : List (Nat × Nat) := [(7, 17), (7, 17), (4, 6)]

def measured : List (Nat × Nat) :=
  selected.map fun s => (s.lemmas.length, s.done)

#guard measured == appendixB

-- foundations `results/experiments.txt`: 64 candidates, 3 kept
#guard candidatosFst.length == 64
#guard selected.length == 3

end MM.Examples.FirstSearch
