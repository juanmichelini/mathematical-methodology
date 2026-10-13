import MathematicalMethodology.Report

/-- `lake exe results` prints the markdown report and exits non-zero if a good
certificate was rejected or a bad one accepted. -/
def main : IO UInt32 := do
  IO.print MM.Report.markdown
  return if MM.Report.allOk then 0 else 1
