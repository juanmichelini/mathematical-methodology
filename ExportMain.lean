import MathematicalMethodology.Export.Lean
import MathematicalMethodology.Export.AppendixB
import MathematicalMethodology.Examples.SecondSearch

/-- `lake exe export-lean > MathematicalMethodology/Generated/FstCandidates.lean`
and `lake exe export-lean appendixB > MathematicalMethodology/Generated/AppendixB.lean`
(the latter runs both searches, about a minute). -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["appendixB"] =>
    IO.print (MM.Export.appendixBFile
      (MM.Examples.FirstSearch.selected ++ MM.Examples.SecondSearch.selected))
  | _ => IO.print MM.Export.fstFile
  return 0
