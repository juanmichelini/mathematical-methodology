/-!
# Enumeration helpers

Ports of the list helpers of foundations `code/Util.hs` that the enumeration uses.
Untrusted: nothing in `Operational/`, `Cert.lean` or `Semantics/` imports this file.
-/

namespace MM.Strategic

/-- Cartesian product of lists, Haskell `hilar`: the *first* list varies fastest.
`hilar [[1,2],[3,4]] = [[1,3],[2,3],[1,4],[2,4]]`. -/
def hilar {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: xss => (hilar xss).flatMap fun hs => xs.map fun x => x :: hs

/-- Haskell `dist n xs`: every way of cutting `xs` into `n` consecutive (possibly
empty) blocks, in the order of the original. -/
def dist {α : Type} : Nat → List α → List (List (List α))
  | 0, _ => []
  | 1, xs => [[xs]]
  | n + 2, [] => [List.replicate (n + 2) []]
  | n + 2, xs =>
    (List.range (xs.length + 1)).flatMap fun m =>
      (dist (n + 1) (xs.drop m)).map fun ys => xs.take m :: ys

/-- Lexicographic `≤` on lists of strings (Haskell `Ord [String]`). -/
def lexLe : List String → List String → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if a = b then lexLe as bs else false

/-- Haskell `sort` on lists of strings. -/
def sortLists (xs : List (List String)) : List (List String) :=
  xs.mergeSort lexLe

/-- Haskell `sort` on strings. -/
def sortStrings (xs : List String) : List String :=
  xs.mergeSort fun a b => decide (a ≤ b)

end MM.Strategic
