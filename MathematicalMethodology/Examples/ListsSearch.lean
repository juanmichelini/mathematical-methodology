import MathematicalMethodology.Examples.Lists
import MathematicalMethodology.Tactical.Search
import MathematicalMethodology.Pretty

/-!
# Example: the search rediscovers the list development

The conjectures of `Examples/Lists.lean` are given to the (untrusted) search with no
certificates.  It must find one for each, in order, and `Cert.check` must accept them.
-/

namespace MM.Examples

open MM

/-- The statements of the list development, without their certificates. -/
def conjectures : List (String × Affirm) := development.map fun (n, g, _) => (n, g)

def found : List (String × Affirm × Option Cert) := searchDevelopment listCtx conjectures []

/-- The development the search produced (only proven lemmas). -/
def foundDevelopment : List (String × Affirm × Cert) :=
  found.filterMap fun (n, g, c) => c.map fun c => (n, g, c)

#guard found.all fun (_, _, c) => c.isSome
#guard foundDevelopment.length = 4

-- The checker accepts everything the search found.
#guard (checkDevelopment listCtx foundDevelopment []).toBool


-- The search finds certificates as short as the hand-written ones.  They are not
-- identical: the search computes eagerly, the hand-written ones interleave computing and
-- rewriting, so only the order of some steps differs.
#guard List.all (List.zipWith (fun (_, _, c) (_, _, h) => decide (c.size ≤ h.size))
  foundDevelopment development) id

-- The search must not "find" a proof of a false statement, and gives up on a variable
-- that has no data type.
#guard (search listCtx [] searchFuel ⟨["List"], revT (.var 0), .var 0⟩).isNone
#guard (search listCtx [] searchFuel ⟨["List"], appendT (.var 0) nilT, nilT⟩).isNone
#guard (search listCtx [] searchFuel ⟨["Elem"], .var 0, consT (.var 0) nilT⟩).isNone

-- Without the lemmas it needs, the harder lemmas are not found.
#guard (search listCtx [] searchFuel revAppend).isNone
#guard (search listCtx [] searchFuel revRev).isNone

end MM.Examples
