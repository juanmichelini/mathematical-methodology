/-!
# Operational level: terms

The operational level defines *what is possible*: the terms of the untyped
lambda calculus with data constructors and `case`, substitution, and the basic
computation rules.  Nothing here makes a choice; it only defines what can be
done.  (In `juanmichelini/foundations` this is `Syntax.hs` and `Compute.hs`.)

Variables are de Bruijn indices, which removes the need for fresh-name
generation and alpha-equivalence.  A `case` alternative with arity `n` binds
`n` variables; variable `0` is the *last* constructor argument.
-/

namespace MM

mutual
  /-- Terms. `const` names a definition looked up in an `Env`. -/
  inductive Term where
    | var   (i : Nat)
    | con   (c : String)
    | const (f : String)
    | app   (f a : Term)
    | abs   (b : Term)
    | cas   (scrut : Term) (alts : Alts)

  /-- Alternatives of a `case`: constructor name, arity, body. -/
  inductive Alts where
    | nil
    | alt (ctor : String) (arity : Nat) (body : Term) (rest : Alts)
end

deriving instance DecidableEq, Repr, Inhabited for Term
deriving instance DecidableEq, Repr, Inhabited for Alts

/-! ## Renaming and substitution -/

/-- Lift a renaming under one binder. -/
def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-- Lift a renaming under `k` binders. -/
def liftRenN : Nat → (Nat → Nat) → (Nat → Nat)
  | 0, ρ => ρ
  | k + 1, ρ => liftRen (liftRenN k ρ)

mutual
  def Term.rename (ρ : Nat → Nat) : Term → Term
    | .var i => .var (ρ i)
    | .con c => .con c
    | .const f => .const f
    | .app f a => .app (f.rename ρ) (a.rename ρ)
    | .abs b => .abs (b.rename (liftRen ρ))
    | .cas s alts => .cas (s.rename ρ) (alts.rename ρ)

  def Alts.rename (ρ : Nat → Nat) : Alts → Alts
    | .nil => .nil
    | .alt c n b rest => .alt c n (b.rename (liftRenN n ρ)) (rest.rename ρ)
end

/-- Lift a substitution under one binder. -/
def upSub (σ : Nat → Term) : Nat → Term
  | 0 => .var 0
  | n + 1 => (σ n).rename Nat.succ

/-- Lift a substitution under `k` binders. -/
def upSubN : Nat → (Nat → Term) → (Nat → Term)
  | 0, σ => σ
  | k + 1, σ => upSub (upSubN k σ)

mutual
  /-- Simultaneous substitution of the free variables. -/
  def Term.subst (σ : Nat → Term) : Term → Term
    | .var i => σ i
    | .con c => .con c
    | .const f => .const f
    | .app f a => .app (f.subst σ) (a.subst σ)
    | .abs b => .abs (b.subst (upSub σ))
    | .cas s alts => .cas (s.subst σ) (alts.subst σ)

  def Alts.subst (σ : Nat → Term) : Alts → Alts
    | .nil => .nil
    | .alt c n b rest => .alt c n (b.subst (upSubN n σ)) (rest.subst σ)
end

/-- Beta reduction: instantiate the bound variable of `b` with `a`. -/
def Term.beta (b a : Term) : Term :=
  b.subst fun
    | 0 => a
    | n + 1 => .var n

/-- Instantiate a `case` alternative of arity `n` with constructor arguments.
Variable `0` is the last argument. -/
def Term.instAlt (n : Nat) (args : List Term) (body : Term) : Term :=
  body.subst fun i => if i < n then args.getD (n - 1 - i) (.var 0) else .var (i - n)

/-- Find the alternative for a constructor. -/
def Alts.find? (c : String) : Alts → Option (Nat × Term)
  | .nil => none
  | .alt d n b rest => if c = d then some (n, b) else rest.find? c

/-- Head and arguments of an application spine. -/
def Term.spine : Term → Term × List Term
  | .app f a => let r := f.spine; (r.1, r.2 ++ [a])
  | t => (t, [])

/-- Apply a head to arguments. -/
def Term.mkApp (h : Term) (args : List Term) : Term :=
  args.foldl Term.app h

/-- Does the term contain a `case` anywhere (outside of alternatives)? -/
def Term.hasCas : Term → Bool
  | .cas .. => true
  | .app f a => f.hasCas || a.hasCas
  | .abs b => b.hasCas
  | _ => false

/-- Size of a term (used for fuel and tests). -/
def Term.size : Term → Nat
  | .app f a => 1 + f.size + a.size
  | .abs b => 1 + b.size
  | .cas s _ => 1 + s.size
  | _ => 1

end MM
