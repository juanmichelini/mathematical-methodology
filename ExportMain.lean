import MathematicalMethodology.Export.Lean
import MathematicalMethodology.Export.AppendixB
import MathematicalMethodology.Export.Proofs
import MathematicalMethodology.Export.Cert
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
  | ["lists"] =>
    match MM.Export.listsFile with
    | .ok txt => IO.print txt
    | .error e => do IO.eprintln s!"cannot export: {e}"; return 1
  | _ => IO.print MM.Export.fstFile
  return 0
