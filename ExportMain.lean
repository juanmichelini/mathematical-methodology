import MathematicalMethodology.Export.Lean

/-- `lake exe export-lean > MathematicalMethodology/Generated/FstCandidates.lean` -/
def main : IO UInt32 := do
  IO.print MM.Export.fstFile
  return 0
