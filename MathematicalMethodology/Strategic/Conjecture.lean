import MathematicalMethodology.Strategic.Enumerate
import MathematicalMethodology.Tactical.Store
import MathematicalMethodology.Strategic.Show

/-!
# Conjecture generation

Port of the conjecture half of foundations `code/Propose.hs`: `saturateTerm`,
`substitutePTT`, `renameReorderVars`, `ampleDep`, `amplePerm`, `ampleAll`, `instanceAny`,
`conjeturasSoloConDep`, `conjeturasSimp`, `conjeturasPerm`, `conjeturasAll`.

**Untrusted.**  A conjecture is only a proposal; proving it is the tactic search's job and
`Cert.check` has the last word.

## Representation

Terms are de Bruijn `Term`s, and a conjecture is an `Affirm`: free variable `i` is
`ctx[i]`, the `i`-th typed variable.  The terms contain no names.

Foundations' variable *names* are kept next to the term (`PTT.vts`) because they are
observable: the statements of Appendix B are printed with them, `masOrd` orders atoms by
name, and the fresh-name procedure is not canonical (`renameReorderVars` renames `a` to `b`
when the term already mentions `a`).  They are produced by the same `freshs` and
`renameReorderVars` as in Haskell and are never read by anything trusted.

`instanceAny` recurses on the tail of the variable list while the term still mentions the
head variable.  Those variables are `frozen`: free in the term, at indices past the context.
-/

namespace MM.Strategic

open MM

/-! ## Fresh names -/

/-- Haskell `infiniteVars`, as many as asked for that are not in `used`: `a … z`, then
`a0 … z0`, `a1 … z1`, …  (Enough rounds are generated to always have `n` names.) -/
def freshNames (used : List String) (n : Nat) : List String :=
  let rounds := (used.length + n) / 26 + 2
  let pool := ("" :: (List.range rounds).map toString).flatMap fun sfx =>
    "abcdefghijklmnopqrstuvwxyz".toList.map fun ch => ch.toString ++ sfx
  (pool.filter (!used.contains ·)).take n

/-! ## Partially typed terms -/

abbrev VTs := List (String × Ty)

/-- Haskell `PartTypedTerm`: a term, its type and its typed free variables (name, type).
Variable `i` of the term is `vts[i]`; indices `vts.length + k` are the `frozen` variables
(free in the term but not part of the context). -/
structure PTT where
  term : Term
  ty : Ty
  vts : VTs
  frozen : VTs := []

def PTT.names (p : PTT) : List String := (p.vts ++ p.frozen).map Prod.fst

/-- Names a term uses (Haskell `usedVars` on atoms: variables and defined functions). -/
def usedNames (names : List String) : Term → List String
  | .var i => [names.getD i "?"]
  | .const f => [f]
  | .app f a => usedNames names f ++ usedNames names a
  | _ => []

/-- Variable occurrences in order (with repetitions). -/
def varOccs : Term → List Nat
  | .var i => [i]
  | .app f a => varOccs f ++ varOccs a
  | _ => []

/-- Free variables and function names in order of first occurrence (Haskell
`nub . freeVars`, restricted to the names that are variables of the context). -/
def occurrenceOrder (t : Term) : List Nat := (varOccs t).eraseDups

/-- Haskell `saturateTerm`: apply an atom to fresh variables, one per parameter. -/
def saturate (e : Term) (t : Ty) : PTT :=
  let (pars, ret) := t.parsAndRet
  let names := freshNames (usedNames [] e) pars.length
  ⟨e.mkApp ((List.range pars.length).map Term.var), ret, names.zip pars, []⟩

/-- Haskell `substitutePTT v (d) (a)`: replace variable `v` of `a` by the term of `d`.
Every variable gets a fresh name; the context is `d`'s variables, then `a`'s others. -/
def substitutePTT (v : Nat) (d a : PTT) : Option PTT :=
  match a.vts[v]? with
  | none => none
  | some (_, r) =>
    if r != d.ty then none else
    let n1 := d.vts.length
    let n2 := a.vts.length
    let used := usedNames d.names d.term ++ usedNames a.names a.term ++ d.names ++ a.names
    let newvars := freshNames used (n1 + (n2 - 1))
    let rank (i : Nat) : Nat := if i < v then i else i - 1
    let σ : Nat → Term := fun i =>
      if i == v then d.term
      else if i < n2 then .var (n1 + rank i)
      else .var (i - 1 + n1)          -- frozen variables stay past the context
    let others := (a.vts.zipIdx.filter fun (_, i) => i != v).map fun ((_, t), _) => t
    let vts' := (newvars.take n1).zip (d.vts.map Prod.snd)
    let wts' := (newvars.drop n1).zip others
    some ⟨a.term.subst σ, a.ty, vts' ++ wts', a.frozen⟩

/-- Haskell `renameReorderVars`: name the variables that occur by position of first
occurrence (using the first fresh names that are not used by the term, sorted), drop the
ones that do not occur, keep the order of the list. -/
def renameReorderVars (p : PTT) : PTT :=
  let occ := (occurrenceOrder p.term).filter (· < p.vts.length)
  let used := usedNames p.names p.term
  let s := sortStrings (freshNames used occ.length)
  let newName (i : Nat) : Option String := (occ.idxOf? i).bind fun k => s[k]?
  let keep := (List.range p.vts.length).filter occ.contains
  let newIdx (i : Nat) : Nat := (keep.idxOf? i).getD i
  let σ : Nat → Term := fun i => if i < p.vts.length then .var (newIdx i) else .var i
  let vts' := keep.filterMap fun i =>
    (newName i).bind fun nm => (p.vts[i]?).map fun (_, t) => (nm, t)
  ⟨p.term.subst σ, p.ty, vts', p.frozen⟩

/-- Put the first variable of the context into the frozen list (recursion of
`instanceAny` on the tail). -/
def PTT.freezeHead (p : PTT) : PTT :=
  match p.vts with
  | [] => p
  | h :: tl =>
    let n := tl.length
    let σ : Nat → Term := fun i => if i == 0 then .var n else if i ≤ n then .var (i - 1) else .var i
    ⟨p.term.subst σ, p.ty, tl, h :: p.frozen⟩

/-- Inverse of `freezeHead`: the most recently frozen variable goes back to the front. -/
def PTT.unfreezeHead (p : PTT) : PTT :=
  match p.frozen with
  | [] => p
  | h :: fr =>
    let n := p.vts.length
    let σ : Nat → Term := fun i => if i == n then .var 0 else if i < n then .var (i + 1) else .var i
    ⟨p.term.subst σ, p.ty, h :: p.vts, fr⟩

/-- Haskell `instanceAny env tenv ins q`: for each variable, either keep it or replace it
by one of the saturated terms `ins` of the same type (in that order, variable by variable). -/
partial def instanceAny (ins : List PTT) (p : PTT) : List PTT :=
  match p.vts with
  | [] => [p]
  | (_, r) :: _ =>
    let q := p.freezeHead
    (ins.filter (·.ty == r)).flatMap fun y =>
      (instanceAny ins q).flatMap fun ab =>
        let pab := ab.unfreezeHead
        pab :: (substitutePTT 0 y pab).toList

/-! ## Environments -/

def atomTerm : Atom → Term
  | .var i => .var i
  | .const f => .const f
  | .con c => .con c

def tenvLookup (tenv : TEnv) (t : Term) : Option Ty := (tenv.find? (·.1 == t)).map (·.2)

/-- Haskell `ampleDep`: the saturated function and its instances by the saturated terms
it depends on (itself last), as one conjecture left-hand side each. -/
def ampleDep (env : Env) (tenv : TEnv) (v : String) : List PTT :=
  match tenvLookup tenv (.const v) with
  | none => []
  | some ty =>
    let a := saturate (.const v) ty
    let deps := (((dependencies env (.const v)).erase (.const v)) ++ [.const v])
    let sorted := deps.mergeSort fun x y =>
      (dependencies env (atomTerm x)).length ≤ (dependencies env (atomTerm y)).length
    let depst := sorted.filterMap fun x => (tenvLookup tenv (atomTerm x)).map fun t => (atomTerm x, t)
    let sdep := depst.map fun (e, t) => saturate e t
    let cands := a :: sdep.flatMap fun d =>
      (a.vts.zipIdx.filter fun ((_, s), _) => s == d.ty).filterMap fun (_, w) =>
        substitutePTT w d a
    (cands.filter (·.vts.length ≤ 3)).map renameReorderVars

/-- Haskell `amplePerm`. -/
def amplePerm (tenv : TEnv) (vs : List String) : List PTT :=
  let svs := vs.filterMap fun v => (tenvLookup tenv (.const v)).map fun t => saturate (.const v) t
  ((svs.flatMap (instanceAny svs)).filter (·.vts.length ≤ 3)).map renameReorderVars

/-- Haskell `ampleAll`: instances of each function by the *other* ones (not the identity). -/
def ampleAll (tenv : TEnv) (vs : List String) : List PTT :=
  let svs := vs.filterMap fun v => (tenvLookup tenv (.const v)).map fun t =>
    (v, saturate (.const v) t)
  (svs.flatMap fun (x, s) =>
    ((instanceAny (svs.filter (·.1 != x) |>.map (·.2)) s).drop 1)).map renameReorderVars

/-! ## Conjectures -/

/-- A conjecture with the (metadata) names of its variables. -/
structure Conj where
  names : List String
  aff : Affirm

/-- The typed variables as atoms of the environment (`vts'` in Haskell). -/
def varAtoms (vts : VTs) : TEnv := vts.zipIdx.map fun ((_, t), i) => (Term.var i, t)

/-- `reject ctx t`: would a stored rule rewrite `t` (Haskell `applyRecT [] rec`)?  `ctx` are
the types of the variables. -/
abbrev Reject := List String → Term → Bool

def noReject : Reject := fun _ _ => false

/-- Haskell `conjeturasSoloConDep`: right-hand sides of type `t` built from the variables
and the environment atoms the term depends on. -/
def conjeturasSoloConDep (reject : Reject) (env : Env) (tenv : TEnv) (p : PTT) : List Conj :=
  let deps := (dependencies env p.term).map atomTerm
  let depst := tenv.filter fun (g, _) => deps.contains g
  let ctx := p.vts.map (·.2.pp)
  (enumAppRec (reject ctx) 2 p.ty (varAtoms p.vts ++ depst)).map fun r =>
    ⟨p.vts.map (·.1), ⟨ctx, p.term, r⟩⟩

/-- Haskell `conjeturasSimp`: only those whose left side is bigger (`fund`). -/
def conjeturasSimp (reject : Reject) (env : Env) (tenv : TEnv) (p : PTT) : List Conj :=
  (conjeturasSoloConDep reject env tenv p).filter fun c => c.aff.lhs.fund env > c.aff.rhs.fund env

/-! ### Ordering atoms by name (`masOrd`) -/

/-- Haskell's `Ord Atm`: variables (and defined functions, which are variables there)
before constructors, by name. -/
def atomKey (names : List String) : Atom → Nat × String
  | .var i => (0, names.getD i "")
  | .const f => (0, f)
  | .con c => (1, c)

def cmpKey (a b : Nat × String) : Ordering :=
  match compare a.1 b.1 with
  | .eq => compare a.2 b.2
  | o => o

/-- Haskell `masOrd`, with atoms compared by name. -/
def masOrdN (names : List String) (t1 t2 : Term) : Ordering :=
  let k := fun (t : Term) => t.argAtoms.map (atomKey names)
  match ((k t1).zipWith cmpKey (k t2)).filter (· != .eq) with
  | o :: _ => o
  | [] => ((t1.heights.zipWith compare t2.heights).filter (· != .eq)).headD .eq

/-- Haskell `conjeturasPerm`: permutations of the left side's atoms, smallest first. -/
def conjeturasPerm (reject : Reject) (tenv : TEnv) (p : PTT) : List Conj :=
  let ctx := p.vts.map (·.2.pp)
  let atoms := (p.term.atoms.map atomTerm).eraseDups
  let depst := tenv.filter fun (g, _) => atoms.contains g
  let rs := (enumAppRec (reject ctx) 2 p.ty (varAtoms p.vts ++ depst)).take 100
  let sorted := rs.mergeSort fun x y => masOrdN p.names x y != .gt
  (sorted.map (fun r => (⟨p.vts.map (·.1), ⟨ctx, p.term, r⟩⟩ : Conj))).filter fun c =>
    soloPermuta c.aff && c.aff.lhs != c.aff.rhs

/-- Haskell `conjeturasAll`. -/
def conjeturasAll (reject : Reject) (tenv : TEnv) (p : PTT) : List Conj :=
  let ctx := p.vts.map (·.2.pp)
  let atoms := (p.term.atoms.map atomTerm).eraseDups
  let depst := tenv.filter fun (g, _) => atoms.contains g
  let rs := (enumAppRec (reject ctx) 2 p.ty (varAtoms p.vts ++ depst)).take 1000
  (rs.map (fun r => (⟨p.vts.map (·.1), ⟨ctx, p.term, r⟩⟩ : Conj))).filter fun c =>
    c.aff.lhs != c.aff.rhs

/-- Haskell `plemas`: the batches of conjectures for a function (the `ampleDep` batches
twice, as in Haskell, then the permutation batches). -/
def plemas (reject : Reject) (env : Env) (tenv : TEnv) (v : String) : List (List Conj) :=
  (ampleDep env tenv v).map (conjeturasSimp reject env tenv) ++
  (ampleDep env tenv v).map (conjeturasSimp reject env tenv) ++
  (amplePerm tenv [v]).map (conjeturasPerm reject tenv)

/-- One line per conjecture, in the format of the Haskell dump used as ground truth:
`a:T b:U |- lhs = rhs`. -/
def Conj.show (c : Conj) : String :=
  " ".intercalate (c.names.zip c.aff.ctx |>.map fun (v, t) => s!"{v}:{t}") ++ " |- " ++
    showNamed c.names c.aff.lhs ++ " = " ++ showNamed c.names c.aff.rhs

end MM.Strategic
