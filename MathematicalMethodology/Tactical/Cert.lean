import MathematicalMethodology.Operational.Compute

/-!
# Tactical level: certificates and the checker

The tactical level defines *how we attempt things*.  A tactic (written later, and
untrusted) searches for a `Cert`.  The only trusted code at this level is
`Cert.check`, which re-verifies a certificate step by step using the operational
level.  (In `juanmichelini/foundations` this corresponds to `Proof` in `Prove.hs`.)

A statement (`Affirm`) is an equation between open terms. Free variable `i` of
the terms has type `ctx[i]`.

## Known limitations (v0)

* Rewriting and matching are untyped: only induction looks at `ctx` types.
* Rewriting and computing only touch *spine positions* (application parts and
  `case` scrutinees), never the inside of a binder or an alternative, so free
  variable indices never shift.
* There is no soundness theorem yet; see the roadmap in `docs/ROADMAP.md`.
-/

namespace MM

/-- `∀ ctx, lhs = rhs`, with free de Bruijn variables typed by `ctx`. -/
structure Affirm where
  ctx : List String
  lhs : Term
  rhs : Term
  deriving DecidableEq, Repr

/-- A data type: constructor names with their field types.  A field is
recursive iff its type is the data type's own name. -/
structure DataDecl where
  name  : String
  ctors : List (String × List String)
  deriving Repr

/-- A rewrite rule.  With `npat > 0` all free variables are pattern variables
(a proven lemma).  With `npat = 0` the rule is ground/rigid (an induction
hypothesis) and matches only syntactically. -/
structure Rule where
  npat : Nat
  lhs  : Term
  rhs  : Term
  deriving Repr

def Affirm.toRule (a : Affirm) : Rule := ⟨a.ctx.length, a.lhs, a.rhs⟩

inductive Side | lhs | rhs
  deriving DecidableEq, Repr

mutual
  /-- Proof certificates. `rule` indexes into the current rule list
  (induction hypotheses first, then proven lemmas). -/
  inductive Cert where
    | refl
    | compute (s : Side) (rest : Cert)
    | rewrite (s : Side) (rule : Nat) (rev : Bool) (rest : Cert)
    | induct  (v : Nat) (cases : Certs)

  /-- One certificate per constructor, in declaration order. -/
  inductive Certs where
    | nil
    | cons (c : Cert) (rest : Certs)
end

/-! ## Matching and rewriting -/

/-- First-order terms: no binders, no `case`. -/
def Term.isFO : Term → Bool
  | .var _ | .con _ | .const _ => true
  | .app f a => f.isFO && a.isFO
  | _ => false

def Term.vars : Term → List Nat
  | .var i => [i]
  | .app f a => f.vars ++ a.vars
  | _ => []

abbrev Binding := List (Nat × Term)

/-- First-order matching of a pattern against a target. -/
def matchFO : Term → Term → Binding → Option Binding
  | .var i, t, b =>
    match b.find? (·.1 = i) with
    | some (_, t0) => if t0 = t then some b else none
    | none => some ((i, t) :: b)
  | .con c, .con d, b => if c = d then some b else none
  | .const f, .const g, b => if f = g then some b else none
  | .app p q, .app s t, b => do
    let b1 ← matchFO p s b
    matchFO q t b1
  | _, _, _ => none

def Term.instFO (b : Binding) : Term → Option Term
  | .var i => (b.find? (·.1 = i)).map (·.2)
  | .con c => some (.con c)
  | .const f => some (.const f)
  | .app f a => do
    let f' ← f.instFO b
    let a' ← a.instFO b
    some (.app f' a')
  | _ => none

def Rule.orient (r : Rule) (rev : Bool) : Rule :=
  if rev then { r with lhs := r.rhs, rhs := r.lhs } else r

/-- Rewrite `t` at the root with rule `r`, if it matches. -/
def Rule.tryRoot (r : Rule) (t : Term) : Option Term :=
  if r.npat = 0 then
    if t = r.lhs then some r.rhs else none
  else if r.lhs.isFO && r.rhs.isFO then
    match matchFO r.lhs t [] with
    | some b =>
      if r.rhs.vars.all (fun i => (b.find? (·.1 = i)).isSome) then r.rhs.instFO b else none
    | none => none
  else none

/-- Rewrite at the first matching spine position (preorder). -/
def Term.rewriteFirst (r : Rule) : Term → Option Term
  | .app f a =>
    match r.tryRoot (.app f a) with
    | some u => some u
    | none =>
      match f.rewriteFirst r with
      | some f' => some (.app f' a)
      | none => (a.rewriteFirst r).map fun a' => .app f a'
  | .cas s alts =>
    match r.tryRoot (.cas s alts) with
    | some u => some u
    | none => (s.rewriteFirst r).map fun s' => .cas s' alts
  | t => r.tryRoot t

/-! ## Induction -/

/-- Substitution that replaces free variable `v` by `img` and closes the gap. -/
def closeGap (v : Nat) (img : Term) : Nat → Term := fun i =>
  if i < v then .var i else if i = v then img else .var (i - 1)

/-- Subgoals and updated rules for induction on variable `v` of goal `g`. -/
def inductCases (g : Affirm) (v : Nat) (d : DataDecl) (rules : List Rule) :
    List (Affirm × List Rule) :=
  let n := g.ctx.length
  let others := g.ctx.eraseIdx v
  d.ctors.map fun (c, fields) =>
    let k := fields.length
    let fieldVars := (List.range k).map fun j => Term.var (n - 1 + j)
    let σ := closeGap v (Term.mkApp (.con c) fieldVars)
    let goal : Affirm := ⟨others ++ fields, g.lhs.subst σ, g.rhs.subst σ⟩
    let ihs : List Rule :=
      (List.range k).filterMap fun j =>
        if fields.getD j "" = d.name then
          let σj := closeGap v (.var (n - 1 + j))
          some ⟨0, g.lhs.subst σj, g.rhs.subst σj⟩
        else none
    let old : List Rule := rules.map fun r =>
      if r.npat = 0 then ⟨0, r.lhs.subst σ, r.rhs.subst σ⟩ else r
    (goal, ihs ++ old)

/-! ## The checker -/

structure Ctx where
  env  : Env
  data : List DataDecl

def Side.get (g : Affirm) : Side → Term
  | .lhs => g.lhs
  | .rhs => g.rhs

def Side.set (g : Affirm) : Side → Term → Affirm
  | .lhs, t => { g with lhs := t }
  | .rhs, t => { g with rhs := t }

/-- Fuel for `computeSafe` inside the checker. -/
def computeFuel : Nat := 200

mutual
  /-- Check that `c` proves `g` using `rules`. -/
  def Cert.check (cx : Ctx) (rules : List Rule) : Cert → Affirm → Except String Unit
    | .refl, g =>
      if g.lhs = g.rhs then .ok () else .error "refl: sides differ"
    | .compute s rest, g =>
      match (s.get g).computeWide cx.env computeFuel with
      | none => .error "compute: no case-free result at any spine position"
      | some t' => rest.check cx rules (s.set g t')
    | .rewrite s i rev rest, g =>
      match rules[i]? with
      | none => .error s!"rewrite: no rule {i}"
      | some r =>
        match (s.get g).rewriteFirst (r.orient rev) with
        | none => .error s!"rewrite: rule {i} does not apply"
        | some t' =>
          if t' = s.get g then .error "rewrite: no progress"
          else rest.check cx rules (s.set g t')
    | .induct v cases, g =>
      match g.ctx[v]? with
      | none => .error "induct: no such variable"
      | some ty =>
        match cx.data.find? (·.name = ty) with
        | none => .error s!"induct: {ty} is not a data type"
        | some d => cases.checkAll cx (inductCases g v d rules)

  /-- Check one certificate per subgoal. -/
  def Certs.checkAll (cx : Ctx) : Certs → List (Affirm × List Rule) → Except String Unit
    | .nil, [] => .ok ()
    | .nil, _ :: _ => .error "induct: missing cases"
    | .cons _ _, [] => .error "induct: too many cases"
    | .cons c rest, (g, rs) :: gs => do
      c.check cx rs g
      rest.checkAll cx gs
end

/-- A development: lemmas proven in order; each proven lemma becomes a rule for
the later ones. Returns the final rule list, or the first error. -/
def checkDevelopment (cx : Ctx) :
    List (String × Affirm × Cert) → List Rule → Except String (List Rule)
  | [], rules => .ok rules
  | (name, g, c) :: rest, rules =>
    match c.check cx rules g with
    | .error e => .error s!"{name}: {e}"
    | .ok () => checkDevelopment cx rest (rules ++ [g.toRule])

end MM
