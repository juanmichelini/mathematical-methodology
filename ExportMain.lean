import MathematicalMethodology.Export.Lean
import MathematicalMethodology.Export.AppendixB
import MathematicalMethodology.Export.Proofs
import MathematicalMethodology.Export.Suite
import MathematicalMethodology.Examples.SecondSearch

/-- `lake exe export-lean > MathematicalMethodology/Generated/FstCandidates.lean`
and `lake exe export-lean appendixB > MathematicalMethodology/Generated/AppendixB.lean`
(the latter runs both searches, about a minute). -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["appendixB"] =>
    IO.print (MM.Export.appendixBFile
      (MM.Examples.FirstSearch.selected ++ MM.Examples.SecondSearch.selected))
  | ["proofs"] =>
    let (txt, bad) := MM.Export.proofsFile
      (MM.Examples.FirstSearch.selected ++ MM.Examples.SecondSearch.selected)
    IO.print txt
    IO.eprintln s!"theorems with no tactic for some step: {bad}"
    if bad != 0 then
      IO.eprintln "INVARIANT VIOLATED (should not happen): a proof the system found has a step with no Lean tactic"
      return 1
  | ["suite"] =>
    let (txt, n, failed, bad) := MM.Export.suiteFile
    IO.print txt
    IO.eprintln s!"theorems: {n}; lemmas the system failed to prove: {failed.length} {failed}; steps with no tactic: {bad}"
    if bad != 0 || failed != MM.Export.suiteAssumed then
      IO.eprintln "INVARIANT VIOLATED (should not happen): every lemma the system proves must have a Lean proof; only the known assumed lemma may be missing"
      return 1
  | _ => IO.print MM.Export.fstFile
  return 0
