import MathematicalMethodology.Tactical.Cert

/-!
# Example: lists, append and reverse

Reproduces, as checked certificates, the headline result of
`juanmichelini/foundations`: `rev (rev xs) = xs`, together with the lemmas it
needs (`append_nil`, `append_assoc`, `rev_append`).

The certificates are written by hand here; discovering them is the job of the
(future, untrusted) tactic and strategy levels.
-/

namespace MM.Examples

open MM

def nilT : Term := .con "nil"
def consT (h t : Term) : Term := Term.mkApp (.con "cons") [h, t]
def appendT (a b : Term) : Term := Term.mkApp (.const "append") [a, b]
def revT (a : Term) : Term := .app (.const "rev") a

/-- `append = λ xs ys. case xs of nil → ys | cons h t → cons h (append t ys)` -/
def appendDef : Term :=
  .abs (.abs (.cas (.var 1)
    (.alt "nil" 0 (.var 0)
    (.alt "cons" 2 (consT (.var 1) (appendT (.var 0) (.var 2)))
    .nil))))

/-- `rev = λ l. case l of nil → nil | cons h t → append (rev t) (cons h nil)` -/
def revDef : Term :=
  .abs (.cas (.var 0)
    (.alt "nil" 0 nilT
    (.alt "cons" 2 (appendT (revT (.var 0)) (consT (.var 1) nilT))
    .nil)))

def listCtx : Ctx where
  env  := [("append", appendDef), ("rev", revDef)]
  data := [{ name := "List", ctors := [("nil", []), ("cons", ["Elem", "List"])] }]

/-! ## Operational level: computing -/

-- `rev (cons a (cons b nil))` evaluates (via the case-free rule) to something
-- built from `append`, and `append` of two concrete lists computes fully.
#guard
  (Term.computeSafe listCtx.env 200
    (appendT (consT (.var 0) nilT) (consT (.var 1) nilT)))
  = some (consT (.var 0) (appendT nilT (consT (.var 1) nilT)))

/-! ## Tactical level: certificates -/

def c1 (c : Cert) : Certs := .cons c .nil
def c2 (a b : Cert) : Certs := .cons a (.cons b .nil)

/-- `∀ x, append x nil = x` -/
def appendNil : Affirm := ⟨["List"], appendT (.var 0) nilT, .var 0⟩

def appendNilCert : Cert :=
  .induct 0 <| c2
    (.compute .lhs .refl)
    (.compute .lhs (.rewrite .lhs 0 false .refl))

/-- `∀ x y z, append (append x y) z = append x (append y z)` -/
def appendAssoc : Affirm :=
  ⟨["List", "List", "List"],
   appendT (appendT (.var 0) (.var 1)) (.var 2),
   appendT (.var 0) (appendT (.var 1) (.var 2))⟩

def appendAssocCert : Cert :=
  .induct 0 <| c2
    (.compute .lhs (.compute .rhs .refl))
    (.compute .lhs (.rewrite .lhs 0 false (.compute .rhs .refl)))

/-- `∀ x y, rev (append x y) = append (rev y) (rev x)` -/
def revAppend : Affirm :=
  ⟨["List", "List"],
   revT (appendT (.var 0) (.var 1)),
   appendT (revT (.var 1)) (revT (.var 0))⟩

def revAppendCert : Cert :=
  .induct 0 <| c2
    (.compute .lhs (.compute .rhs (.rewrite .rhs 0 false .refl)))
    (.compute .lhs (.rewrite .lhs 0 false (.rewrite .lhs 2 false (.compute .rhs .refl))))

/-- `∀ x, rev (rev x) = x` -/
def revRev : Affirm := ⟨["List"], revT (revT (.var 0)), .var 0⟩

def revRevCert : Cert :=
  .induct 0 <| c2
    (.compute .lhs .refl)
    (.compute .lhs (.rewrite .lhs 3 false (.rewrite .lhs 0 false
      (.compute .lhs (.compute .lhs .refl)))))

def development : List (String × Affirm × Cert) :=
  [ ("append_nil",   appendNil,   appendNilCert)
  , ("append_assoc", appendAssoc, appendAssocCert)
  , ("rev_append",   revAppend,   revAppendCert)
  , ("rev_rev",      revRev,      revRevCert) ]

/-- Show the error, if any (for `#eval` while developing certificates). -/
def result : String :=
  match checkDevelopment listCtx development [] with
  | .ok rules => s!"ok: {rules.length} rules"
  | .error e => s!"error: {e}"

#eval result

#guard (checkDevelopment listCtx development []).toBool

/-! ## The checker rejects bad certificates -/

def isError {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

/-- Developments the checker must reject: a description and the development.
Shared by the `#guard` below and by the generated report (`results/report.md`). -/
def negatives : List (String × List (String × Affirm × Cert)) :=
  [ ("false statement `append x nil = nil`, with the certificate of a true lemma",
     [("false", ⟨["List"], appendT (.var 0) nilT, nilT⟩, appendNilCert)])
  , ("false statement `rev x = x`, with an unrelated certificate",
     [("false", ⟨["List"], revT (.var 0), .var 0⟩, appendNilCert)])
  , ("reference to a rule that does not exist",
     [("bad", appendNil,
        .induct 0 <| c2 (.compute .lhs .refl)
          (.compute .lhs (.rewrite .lhs 7 false .refl)))])
  , ("too few cases for an induction",
     [("bad", appendNil, .induct 0 (c1 (.compute .lhs .refl)))])
  , ("lemma used before it is proven (rev_rev proved first)",
     [("rev_rev", revRev, revRevCert)])
  , ("induction on a variable that is not of a data type",
     [("bad", ⟨["Elem"], .var 0, .var 0⟩, .induct 0 .nil)]) ]

#guard negatives.all fun (_, dev) => isError (checkDevelopment listCtx dev [])

end MM.Examples
