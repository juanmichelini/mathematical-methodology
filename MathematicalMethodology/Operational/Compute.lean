import MathematicalMethodology.Operational.Term

/-!
# Operational level: computation

Computation rules: unfolding a definition (delta), beta, and `case` on a
constructor.  `Term.step` is the leftmost-outermost step along the spine, and
`Term.computeSafe` is the Haskell `computeDontEndInCas`: run steps, and keep the
last result that contains no `case` (so we never leave a stuck `case` behind).
-/

namespace MM

/-- Definitions, by name. -/
abbrev Env := List (String × Term)

def Env.lookup (env : Env) (f : String) : Option Term :=
  (env.find? (·.1 = f)).map (·.2)

/-- One computation step at the head of the spine (leftmost-outermost). -/
def Term.step (env : Env) : Term → Option Term
  | .const f => env.lookup f
  | .app (.abs b) a => some (Term.beta b a)
  | .app f a => (f.step env).map fun f' => .app f' a
  | .cas s alts =>
    match s.spine with
    | (.con c, args) =>
      match alts.find? c with
      | some (n, body) => if args.length = n then some (Term.instAlt n args body) else none
      | none => none
    | _ => (s.step env).map fun s' => .cas s' alts
  | _ => none

/-- Run up to `fuel` steps; return the last `case`-free result, if any step
produced one. -/
def Term.computeSafe (env : Env) (fuel : Nat) (t : Term) : Option Term :=
  go fuel t none
where
  go : Nat → Term → Option Term → Option Term
    | 0, _, best => best
    | n + 1, t, best =>
      match t.step env with
      | none => best
      | some t' => go n t' (if t'.hasCas then best else some t')

/-- `computeSafe` at the root, but only if it made progress. -/
def Term.computeHere (env : Env) (fuel : Nat) (t : Term) : Option Term :=
  match t.computeSafe env fuel with
  | some u => if u = t then none else some u
  | none => none

/-- Like `computeHere`, but searches the first spine position (preorder: root,
then function part, then argument, then `case` scrutinee) where it succeeds.
Never enters a binder or an alternative, so free variable indices are stable. -/
def Term.computeWide (env : Env) (fuel : Nat) : Term → Option Term
  | .app f a =>
    match Term.computeHere env fuel (.app f a) with
    | some u => some u
    | none =>
      match f.computeWide env fuel with
      | some f' => some (.app f' a)
      | none => (a.computeWide env fuel).map fun a' => .app f a'
  | .cas s alts =>
    match Term.computeHere env fuel (.cas s alts) with
    | some u => some u
    | none => (s.computeWide env fuel).map fun s' => .cas s' alts
  | t => Term.computeHere env fuel t

end MM
