import MathematicalMethodology.Export.Cert
import MathematicalMethodology.Generated.Lists

/-!
# The checker's certificates exported to Lean: tests

`Generated/Lists.lean` holds `append`, `rev` and the four lemmas of `Examples/Lists.lean`
(`append_nil`, `append_assoc`, `rev_append`, `rev_rev`) as plain Lean, with proofs printed from
the `Cert`s that `Cert.check` accepts.  It is a module of the library, so `lake build` makes
**Lean's kernel check the theorems independently of `Cert.check`**.  Here:

* the committed file equals the generator's output;
* the exported functions run;
* every development the checker rejects (the `negatives` of `Examples/Lists.lean`) is refused by
  the exporter, and so is a certificate with a missing case.
-/

namespace MM.Examples.ExportLists

open MM MM.Export

#guard exportIs (exportCerts "rev (rev xs) = xs and its lemmas: the certificates of Cert.check as Lean theorems."
    "ListsEx" listCtx development) (include_str "../Generated/Lists.lean")

-- one theorem per lemma
#guard ((include_str "../Generated/Lists.lean").splitOn "\ntheorem ").length - 1 = development.length

/-! ## The exported functions run -/

open ListsEx

private def l (xs : List Nat) : ExList Nat := xs.foldr ExList.cons ExList.nil

#guard append (l [1, 2]) (l [3]) = l [1, 2, 3]
#guard rev (l [1, 2, 3]) = l [3, 2, 1]
#guard rev (rev (l [4, 5, 6])) = l [4, 5, 6]

-- the exported theorems can be used like any other
example (xs : ExList Nat) : rev (rev xs) = xs := rev_rev xs
example (xs ys : ExList Nat) : rev (append xs ys) = append (rev ys) (rev xs) := rev_append xs ys

/-! ## The exporter refuses what the checker rejects -/

-- every bad development of `Examples/Lists.lean`
#guard negatives.all fun (_, dev) => !(exportCerts "t" "N" listCtx dev).toBool

-- a certificate with a missing case
#guard !(exportCerts "t" "N" listCtx
  [("append_nil", appendNil, .induct 0 (c1 (.compute .lhs .refl)))]).toBool

-- the empty development exports (no theorems)
#guard (exportCerts "t" "N" listCtx []).toBool

end MM.Examples.ExportLists
