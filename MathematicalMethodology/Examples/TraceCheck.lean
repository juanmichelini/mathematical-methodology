import MathematicalMethodology.Trace
import MathematicalMethodology.Examples.Lists

/-!
# Traces: small checks

The trace printers on small inputs (the full run is `lake exe trace`, which is not part of the
build because it takes minutes).
-/

namespace MM.Examples.TraceCheck

open MM MM.Trace MM.Examples

-- the de Bruijn view of `append`
#guard dbTerm appendDef ==
  "(λ. (λ. (case #1 {nil/0 → #0; cons/2 → ((cons #1) ((@append #0) #2))})))"

#guard dbAffirm appendNil == "[List] ((@append #0) nil) = #0"

-- why a proof gave up
private def c0 : Conj := ⟨["x"], appendNil⟩
#guard proofReason .done == none
#guard proofReason (.step c0 .noIdea .fail) == some "no rule applies"
#guard proofReason (.step c0 .loop .fail) == some "cycle cut"
#guard proofReason .fail == some "step budget exhausted"
#guard proofReason (.step c0 .triv (.step c0 .noIdea .fail)) == some "no rule applies"

-- counting
#guard countBy ["a", "b", "a"] == [("a", 2), ("b", 1)]

end MM.Examples.TraceCheck
