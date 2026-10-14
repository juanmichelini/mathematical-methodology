import MathematicalMethodology.Strategic.SecondSearch
import MathematicalMethodology.Examples.FirstSearch

/-!
# The second search, against the Haskell

Foundations `Main.candidatosSnd` (the 164 candidates, in order) and `Main.namedSndSel` (the
functions `f3 … f30`), printed by `scripts/haskell/SndSel.hs`: for each function the
definition with Haskell's binder names, type, variable names used, lemmas and finished
proofs.  Together with the first search these are the 31 functions of the thesis' Appendix B.
-/

namespace MM.Examples.SecondSearch

open MM MM.Strategic MM.Examples.FirstSearch

def selected : List Selected := selectSecond MM.Examples.FirstSearch.selected 30

def candidateLines : List String :=
  (candidatosSnd MM.Examples.FirstSearch.selected).map fun (e, t) => showFun e ++ "  ::  " ++ t.pp

def dump : String :=
  "\n".intercalate (
    s!"## candidates {candidateLines.length}" :: candidateLines ++ selected.map Selected.dump) ++ "\n"

/-- From foundations `results/appendixB_comparison.md` (thesis Appendix B): lemmas and
finished proofs of f0 … f30. -/
def appendixB : List (Nat × Nat) :=
  [(7, 17), (7, 17), (4, 6), (3, 5), (4, 9), (3, 9), (3, 6), (3, 7), (3, 7), (3, 6), (3, 7),
   (3, 7), (7, 14), (5, 10), (4, 7), (4, 7), (4, 10), (4, 8), (4, 8), (4, 8), (4, 7), (4, 8),
   (4, 8), (4, 8), (4, 8), (3, 5), (3, 9), (4, 6), (5, 10), (3, 5), (3, 9)]

/-- Lemmas and finished proofs of f0 … f30 as we find them. -/
def measured : List (Nat × Nat) :=
  (MM.Examples.FirstSearch.selected ++ selected).map fun s => (s.lemmas.length, s.done)

-- foundations `results/experiments.txt`: "second search candidates: 164", and the same
-- candidates, in the same order, as the Haskell prints
#guard candidateLines.length == 164

#guard (("## candidates 164" :: candidateLines).take 165) ==
  ((include_str "../../fixtures/haskell/snd_sel.txt").splitOn "\n").take 165

end MM.Examples.SecondSearch
