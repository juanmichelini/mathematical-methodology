import MathematicalMethodology.Export.Lean
import MathematicalMethodology.Strategic.SecondSearch

/-!
# Export of the functions of Appendix B

The 31 functions `f0 … f30` of the thesis (`Strategic/FirstSearch.lean`,
`Strategic/SecondSearch.lean`) as plain Lean, in order, so that the second-search functions
can call the first-search ones (`f3` = reverse calls `f2` = append).  Untrusted.
-/

namespace MM.Export

open MM.Strategic

def appendixBFile (sel : List Selected) : String :=
  exportFile "The 31 functions f0..f30 of Appendix B of the thesis, as plain Lean." "AppB"
    datas (sel.map fun s => (s.name, s.ty, s.def_))

end MM.Export
