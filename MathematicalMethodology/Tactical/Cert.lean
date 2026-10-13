import MathematicalMethodology.Operational.Compute
import MathematicalMethodology.Operational.Scope

/-!
# Tactical level: certificates and the checker

The tactical level defines *how we attempt things*.  A tactic (written later, and
untrusted) searches for a `Cert`.  The only trusted code at this level is
`Cert.check`, which re-verifies a certificate step by step using the operational
level.  (In `juanmichelini/foundations` this corresponds to `Proof` in `Prove.hs`.)

A statement (`Affirm`) is an equation between open terms. Free variable `i` of
the terms has type `ctx[i]`.

## Known limitations (v0)

* Rewriting and computing only touch *spine positions* (application parts and
  `case` scrutinees), never the inside of a binder or an alternative, so free
  variable indices never shift.
* Lemma rules only rewrite first-order terms, and every instance of a lemma must be
  well typed according to the first-order signatures in `Ctx` (`Ctx.typeOf`).
* Soundness of `Cert.check` is proved in `Semantics/CheckSound.lean`, under explicit
  assumptions on the environment, data types and signatures.
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

/-- A rewrite rule.  With `tys ≠ []` the free variables `0 … tys.length-1` are pattern
variables of the given types (a proven lemma).  With `tys = []` the rule is rigid (an
induction hypothesis) and matches only syntactically. -/
structure Rule where
  tys : List String
  lhs : Term
  rhs : Term
  deriving Repr

def Affirm.toRule (a : Affirm) : Rule := ⟨a.ctx, a.lhs, a.rhs⟩

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

/-! ## Typing of first-order terms -/

/-- The checker's context: definitions, data types, and first-order signatures
(`name, argument types, result type`) of the defined functions. -/
structure Ctx where
  env  : Env
  data : List DataDecl
  sigs : List (String × List String × String)

/-- Argument types and data type of a constructor. -/
def Ctx.ctorSig (cx : Ctx) (c : String) : Option (List String × String) :=
  cx.data.findSome? fun d => (d.ctors.find? (·.1 = c)).map fun p => (p.2, d.name)

def Ctx.funSig (cx : Ctx) (f : String) : Option (List String × String) :=
  (cx.sigs.find? (·.1 = f)).map (·.2)

/-- Type of a first-order term in a variable context: the types of the arguments it
still expects, and its result type.  Only well-typed applications are accepted. -/
def Ctx.typeOf (cx : Ctx) (ctx : List String) : Term → Option (List String × String)
  | .var i => (ctx[i]?).map fun ty => ([], ty)
  | .con c => cx.ctorSig c
  | .const f => cx.funSig f
  | .app f a =>
    match cx.typeOf ctx f, cx.typeOf ctx a with
    | some (t :: ts, r), some ([], u) => if u = t then some (ts, r) else none
    | _, _ => none
  | _ => none

/-! ## Matching and rewriting -/

/-- First-order terms: no binders, no `case`. -/
def Term.isFO : Term → Bool
  | .var _ | .con _ | .const _ => true
  | .app f a => f.isFO && a.isFO
  | _ => false

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

/-- Rewrite `t` at the root with rule `r`, if it matches.  A lemma rule must be
first-order, bind every pattern variable, and every bound term must have the
declared type of its pattern variable (in the goal's variable context `ctx`). -/
def Rule.tryRoot (cx : Ctx) (ctx : List String) (r : Rule) (t : Term) : Option Term :=
  if r.tys.isEmpty then
    if t = r.lhs then some r.rhs else none
  else if r.lhs.isFO && r.rhs.isFO then
    match matchFO r.lhs t [] with
    | some b =>
      if (List.range r.tys.length).all (fun i =>
          (b.find? (·.1 = i)).any fun p =>
            decide (cx.typeOf ctx p.2 = some ([], r.tys.getD i "")))
      then r.rhs.instFO b else none
    | none => none
  else none

/-- Rewrite at the first matching spine position (preorder). -/
def Term.rewriteFirst (cx : Ctx) (ctx : List String) (r : Rule) : Term → Option Term
  | .app f a =>
    match r.tryRoot cx ctx (.app f a) with
    | some u => some u
    | none =>
      match f.rewriteFirst cx ctx r with
      | some f' => some (.app f' a)
      | none => (a.rewriteFirst cx ctx r).map fun a' => .app f a'
  | .cas s alts =>
    match r.tryRoot cx ctx (.cas s alts) with
    | some u => some u
    | none => (s.rewriteFirst cx ctx r).map fun s' => .cas s' alts
  | t => r.tryRoot cx ctx t

/-! ## Induction -/

/-- Substitution that replaces free variable `v` by `img` and closes the gap. -/
def closeGap (v : Nat) (img : Term) : Nat → Term := fun i =>
  if i < v then .var i else if i = v then img else .var (i - 1)

/-- Variables standing for the `k` fields of a constructor, placed after the `n - 1`
remaining variables. -/
def fieldVars (n k : Nat) : List Term := (List.range k).map fun j => Term.var (n - 1 + j)

/-- Replace variable `v` (of a context of size `n`) by the constructor `c` applied to
fresh field variables, closing the gap. -/
def caseSubst (n v : Nat) (c : String) (k : Nat) : Nat → Term :=
  closeGap v (Term.mkApp (.con c) (fieldVars n k))

/-- The induction hypothesis for the `j`-th field: the goal with `v` replaced by it. -/
def ihRule (g : Affirm) (v j : Nat) : Rule :=
  let σj := closeGap v (.var (g.ctx.length - 1 + j))
  ⟨[], g.lhs.subst σj, g.rhs.subst σj⟩

/-- The subgoal (and its rules) of induction on variable `v` of goal `g` for the
constructor `cf = (name, field types)` of the data type called `dname`. -/
def inductCase (g : Affirm) (v : Nat) (dname : String) (rules : List Rule)
    (cf : String × List String) : Affirm × List Rule :=
  let σ := caseSubst g.ctx.length v cf.1 cf.2.length
  let goal : Affirm := ⟨g.ctx.eraseIdx v ++ cf.2, g.lhs.subst σ, g.rhs.subst σ⟩
  let ihs : List Rule :=
    (List.range cf.2.length).filterMap fun j =>
      if cf.2.getD j "" = dname then some (ihRule g v j) else none
  -- Rigid rules (induction hypotheses of enclosing inductions) are dropped: they are
  -- about the variable being eliminated.  Lemma rules do not depend on the goal.
  let old : List Rule := rules.filter fun r => !r.tys.isEmpty
  (goal, ihs ++ old)

/-- Subgoals and updated rules for induction on variable `v` of goal `g`, one per
constructor in declaration order. -/
def inductCases (g : Affirm) (v : Nat) (d : DataDecl) (rules : List Rule) :
    List (Affirm × List Rule) :=
  d.ctors.map (inductCase g v d.name rules)

/-! ## The checker -/

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
        match (s.get g).rewriteFirst cx g.ctx (r.orient rev) with
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
        | some d =>
          if g.lhs.scoped g.ctx.length && g.rhs.scoped g.ctx.length then
            cases.checkAll cx (inductCases g v d rules)
          else .error "induct: statement mentions variables outside its context"

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
