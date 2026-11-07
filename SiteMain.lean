import MathematicalMethodology.Site

/-- `lake exe site-data > results/site-data.json` (runs both searches, about two minutes). -/
def main : IO UInt32 := do
  IO.println (MM.Site.siteData.pretty 100)
  return 0
