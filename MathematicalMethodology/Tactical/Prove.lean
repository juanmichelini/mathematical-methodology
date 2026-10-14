import MathematicalMethodology.Tactical.Store

/-!
# Tactical level: `mainTactic` as in foundations (untrusted)

A faithful port of the proof search of `juanmichelini/foundations` `code/Prove.hs`:
`mainTactic`, `applyRec`, `indcFst`, `cutSingleStepCycles`, `giveUp`, `prove`, with the
`Proof` trees it builds.  It differs from `Tactical/Search.lean` (which produces `Cert`s for
the checker) in exactly the places that decide *which* lemmas are found:

* **names.**  Atoms are ordered by name (`masOrd`), so a goal carries the names of its
  variables as metadata (`Conj.names`).  Terms stay de Bruijn.
* **induction hypotheses are lemmas**, quantified over the remaining variables, not rigid
  rules; the fields introduced by an induction are *opaque constants* (`Term.const k`), the
  way Haskell has free variables that are not in the quantifier list.
* **the budget** is Haskell's: the proof tree is cut after `n` steps, cumulatively over the
  cases of an induction (`giveUp`), and 2- and 3-step cycles are cut first.
* **computation** is `cNotCase`: unfold the head function and reduce, but only if no `case`
  is left in the result.

Nothing here is trusted: the result is a proposal.  Turning a found proof into a `Cert`
for `Cert.check` is separate.
-/

namespace MM

/-! ## Named statements -/

/-- A statement together with the (metadata) names of its quantified variables; variable
`i` of the terms is `names[i]`, of type `aff.ctx[i]`. -/
structure Conj where
  names : List String
  aff : Affirm

def Conj.flip (c : Conj) : Conj := { c with aff := c.aff.flip }

instance : BEq Conj := ⟨fun a b => a.names == b.names && a.aff == b.aff⟩

/-! ### Ordering atoms by name (Haskell `Ord Atm`, `masOrd`) -/

/-- Variables and defined functions (variables in Haskell) before constructors, by name. -/
def atomKey (names : List String) : Atom → Nat × String
  | .var i => (0, names.getD i "")
  | .const f => (0, f)
  | .con c => (1, c)

def cmpKey (a b : Nat × String) : Ordering :=
  match compare a.1 b.1 with
  | .eq => compare a.2 b.2
  | o => o

/-- Haskell `masOrd`, each term with the names of its own variables. -/
def masOrdNN (n1 : List String) (t1 : Term) (n2 : List String) (t2 : Term) : Ordering :=
  let k1 := t1.argAtoms.map (atomKey n1)
  let k2 := t2.argAtoms.map (atomKey n2)
  match (k1.zipWith cmpKey k2).filter (· != .eq) with
  | o :: _ => o
  | [] => ((t1.heights.zipWith compare t2.heights).filter (· != .eq)).headD .eq

def masOrdN (names : List String) (t1 t2 : Term) : Ordering := masOrdNN names t1 names t2

/-! ## Computation: `cWide`, `cNotCase` -/

/-- Haskell `cWide`: the first position (root, function part, argument, `case` scrutinee,
body of a lambda) where `cr` applies. -/
def cWide (cr : Term → Option Term) : Term → Option Term
  | .app e f =>
    match cr (.app e f) with
    | some u => some u
    | none =>
      match cWide cr e with
      | some e' => some (.app e' f)
      | none => (cWide cr f).map fun f' => .app e f'
  | .cas e alts =>
    match cr (.cas e alts) with
    | some u => some u
    | none => (cWide cr e).map fun e' => .cas e' alts
  | .abs b =>
    match cr (.abs b) with
    | some u => some u
    | none => (cWide cr b).map Term.abs
  | t => cr t

/-- Haskell `cApp`: beta at the root. -/
def cApp : Term → Option Term
  | .app (.abs b) a => some (Term.beta b a)
  | _ => none

/-- Haskell `cCas`: `case` of a constructor application, at the root. -/
def cCas : Term → Option Term
  | .cas e alts =>
    match e.spine with
    | (.con c, args) =>
      match alts.find? c with
      | some (n, body) => if args.length == n then some (Term.instAlt n args body) else none
      | none => none
    | _ => none
  | _ => none

/-- Haskell `repetir`: apply `f` as long as it applies; `none` if it never did. -/
def repetir (f : Term → Option Term) : Nat → Term → Option Term
  | 0, _ => none
  | fuel + 1, x =>
    match f x with
    | none => none
    | some y => (repetir f fuel y).orElse fun _ => some y

/-- One beta step if there is one anywhere, else one `case` step. -/
def betaOrCase (u : Term) : Option Term :=
  match cWide cApp u with
  | some v => some v
  | none => cWide cCas u

/-- Does the variable with de Bruijn index `idx` get scrutinised by a `case` (Haskell
`caseOn`)? -/
def caseOn (idx : Nat) : Term → Bool
  | .app y b => caseOn idx y || caseOn idx b
  | .abs b => caseOn (idx + 1) b
  | .cas y alts =>
    (y == .var idx) || altsCaseOn idx alts
  | _ => false
where
  altsCaseOn (idx : Nat) : Alts → Bool
    | .nil => false
    | .alt _ n b rest => caseOn (idx + n) b || altsCaseOn idx rest

/-- Haskell `paramsWithCase`: for each parameter of a definition, is it scrutinised? -/
def paramsWithCase (x : Term) : List Bool :=
  let rec lams : Term → Nat
    | .abs b => 1 + lams b
    | _ => 0
  let k := lams x
  let rec body : Term → Term
    | .abs b => body b
    | t => t
  (List.range k).map fun i => caseOn (k - 1 - i) (body x)

/-- Haskell `cNotCase`: unfold the head function and reduce as far as possible, but only
if no `case` is left. -/
def cNotCase (env : Env) (e : Term) : Option Term :=
  match e.spine with
  | (.const f, args) =>
    match env.lookup f with
    | none => none
    | some x =>
      let pwc := paramsWithCase x
      let headed := ((args.zip pwc).filter (·.2)).all fun (a, _) =>
        match a.spine.1 with
        | .abs _ | .cas .. => false
        | _ => true
      if !headed then none else
      match repetir betaOrCase 10000 (x.mkApp args) with
      | none => none
      | some a => if a.hasCas then none else some a
  | _ => none

/-! ## Rewriting with a lemma (`instanciar`, `aLemma`) -/

/-- Haskell `instanciar`: match the pattern (variables are the lemma's quantified
variables; constants and constructors must be equal). -/
def instanciar : Term → Term → List (Nat × Term) → Option (List (Nat × Term))
  | .var i, t, b =>
    match b.find? (·.1 == i) with
    | some (_, t0) => if t0 == t then some b else none
    | none => some ((i, t) :: b)
  | .con c, .con k, b => if c == k then some b else none
  | .const f, .const g, b => if f == g then some b else none
  | .app p q, .app s t, b => do
    let b1 ← instanciar p s b
    instanciar q t b1
  | _, _, _ => none

/-- Substitute the bound terms for the variables of a lemma's right-hand side; `none` if a
variable is not bound (Haskell would leave a free variable that can capture a goal's). -/
def instRhs (b : List (Nat × Term)) : Term → Option Term
  | .var i => (b.find? (·.1 == i)).map (·.2)
  | .con c => some (.con c)
  | .const f => some (.const f)
  | .app f a => do
    let f' ← instRhs b f
    let a' ← instRhs b a
    some (.app f' a')
  | _ => none

/-- Haskell `aLemma`: rewrite at the root with the lemma `l` if it matches. -/
def aLemma (l : Conj) (t : Term) : Option Term :=
  match instanciar l.aff.lhs t [] with
  | some b => instRhs b l.aff.rhs
  | none => none

/-- Haskell `cBottomUp`. -/
def cBottomUp (cr : Term → Option Term) : Term → Option Term
  | .app x y =>
    match cBottomUp cr x with
    | some x' => some (.app x' y)
    | none =>
      match cBottomUp cr y with
      | some y' => some (.app x y')
      | none => cr (.app x y)
  | .var i => cr (.var i)
  | .con c => cr (.con c)
  | .const f => cr (.const f)
  | _ => none

/-! ## The store of lemmas (`Rec`), with names -/

structure HRec where
  simp : List Conj := []
  flod : List Conj := []
  floe : List Conj := []
  reor : List Conj := []
  basu : List Conj := []

def permutaC (c : Conj) : Bool :=
  let key := fun (t : Term) => t.atoms.map (atomKey c.names)
  let srt := fun (l : List (Nat × String)) =>
    l.mergeSort fun x y => cmpKey x y != .gt
  srt (key c.aff.lhs) == srt (key c.aff.rhs)

/-- Haskell `addAffirm`. -/
def HRec.add (env : Env) (r : HRec) (l : Conj) : HRec :=
  let fa := l.aff.lhs.fund env
  let fb := l.aff.rhs.fund env
  let l' := l.flip
  let gap (a : Conj) : Int := (a.aff.lhs.fund env : Int) - (a.aff.rhs.fund env : Int)
  let compF (a b : Conj) : Ordering := compare (gap a) (gap b)
  let compSnd (a b : Conj) : Ordering := masOrdNN a.names a.aff.rhs b.names b.aff.rhs
  if fa > fb then { r with simp := insertBy compF l r.simp }
  else if fa < fb then { r with simp := insertBy compF l' r.simp }
  else if permutaC l then { r with reor := insertBy compSnd l (insertBy compSnd l' r.reor) }
  else { r with basu := l :: r.basu }

def HRec.addAll (env : Env) (r : HRec) (ls : List Conj) : HRec := ls.foldl (HRec.add env) r

/-! ## Comments and proofs -/

inductive Reason | simp | flod | floe | reor
  deriving DecidableEq, Repr

inductive SideComment where
  | compute
  | lemma (r : Reason) (a : Conj)

inductive Comment where
  | noIdea
  | triv
  | loop
  | left (s : SideComment)
  | right (s : SideComment)
  | both (s t : SideComment)
  | induction (v : String)
  | caso (v : String)

/-- Haskell `Proof`. -/
inductive Proof where
  | fail
  | done
  | step (a : Conj) (c : Comment) (p : Proof)
  | ind (a : Conj) (c : Comment) (cases : List (Comment × List Conj × Proof))

mutual
  def Proof.complete : Proof → Bool
    | .done => true
    | .fail => false
    | .step _ _ p => p.complete
    | .ind _ _ cs => Proof.allComplete cs
  def Proof.allComplete : List (Comment × List Conj × Proof) → Bool
    | [] => true
    | (_, _, p) :: r => p.complete && Proof.allComplete r
end

def Proof.head : Proof → Option Conj
  | .step a _ _ => some a
  | .ind a _ _ => some a
  | _ => none

mutual
  /-- Haskell `largo`. -/
  def Proof.size : Proof → Nat
    | .done => 0
    | .fail => 0
    | .step _ _ p => 1 + p.size
    | .ind _ _ cs => 1 + Proof.sizeAll cs
  def Proof.sizeAll : List (Comment × List Conj × Proof) → Nat
    | [] => 0
    | (_, _, p) :: r => p.size + Proof.sizeAll r
end

/-! ## Tactics -/

/-- What the search knows about the world. -/
structure PCtx where
  env : Env
  data : List DataDecl
  /-- Names used by the variables of the definitions in `env` (Haskell's binder names):
fresh names for the fields introduced by an induction avoid them. -/
  defNames : List String := []

/-- Haskell `bothSides`. -/
def bothSides (f : Term → Option (SideComment × Term)) (c : Conj) : Option (Comment × Conj) :=
  match f c.aff.lhs, f c.aff.rhs with
  | some (a, l), some (b, r) => some (.both a b, { c with aff := { c.aff with lhs := l, rhs := r } })
  | none, some (b, r) => some (.right b, { c with aff := { c.aff with rhs := r } })
  | some (a, l), none => some (.left a, { c with aff := { c.aff with lhs := l } })
  | none, none => none

/-- Haskell `applyLemmasC`: the first lemma of the list that applies somewhere. -/
def applyLemmasC (cr : (Term → Option Term) → Term → Option Term) (ls : List Conj) (t : Term) :
    Option (Conj × Term) :=
  ls.findSome? fun u => (cr (aLemma u) t).map fun w => (u, w)

/-- Haskell `applyRec`: stored lemmas by class (simp, flod, floe, then reor with its
`masOrd` guard), on each side. -/
def applyRecH (rec : HRec) (c : Conj) : Option (Comment × Conj) :=
  let side (r : Reason) (ls : List Conj) (cr : (Term → Option Term) → Term → Option Term) :=
    bothSides (fun t => (applyLemmasC cr ls t).map fun (l, w) => (.lemma r l, w)) c
  let wide : (Term → Option Term) → Term → Option Term := cWide
  let guarded : (Term → Option Term) → Term → Option Term := fun f =>
    cBottomUp fun x => (f x).filter fun y => masOrdN c.names x y == .gt
  (side .simp rec.simp wide).orElse fun _ =>
  (side .flod rec.flod wide).orElse fun _ =>
  (side .floe rec.floe wide).orElse fun _ =>
  side .reor rec.reor guarded

/-- Haskell `applyRecT env rec t` (no goal variables): does some stored lemma rewrite `t`?
`names` are the names of the variables `t` mentions. -/
def applyRecT (rec : HRec) (names : List String) (t : Term) : Bool :=
  let wide : (Term → Option Term) → Term → Option Term := cWide
  let guarded : (Term → Option Term) → Term → Option Term := fun f =>
    cBottomUp fun x => (f x).filter fun y => masOrdN names x y == .gt
  (applyLemmasC wide rec.simp t).isSome || (applyLemmasC wide rec.flod t).isSome ||
  (applyLemmasC wide rec.floe t).isSome || (applyLemmasC guarded rec.reor t).isSome

/-- Haskell `computeDontEndInCas`. -/
def computeDontEndInCas (env : Env) (t : Term) : Option (SideComment × Term) :=
  (cWide (cNotCase env) t).map fun h => (.compute, h)

/-! ### Induction -/

/-- Names used by a term (variables and defined functions). -/
def namesUsed (names : List String) : Term → List String := fun t => go t
where
  go : Term → List String
    | .var i => [names.getD i "?"]
    | .const f => [f]
    | .app f a => go f ++ go a
    | _ => []

/-- Haskell `infiniteVars` minus `used`, first `n`. -/
def freshN (used : List String) (n : Nat) : List String :=
  let rounds := (used.length + n) / 26 + 2
  let pool := ("" :: (List.range rounds).map toString).flatMap fun sfx =>
    "abcdefghijklmnopqrstuvwxyz".toList.map fun ch => ch.toString ++ sfx
  (pool.filter (!used.contains ·)).take n

/-- Replace variable 0 by `img` and renumber the others (`i+1 ↦ i`). -/
def dropFirstVar (img : Term) : Term → Term := fun t => t.subst fun i =>
  if i == 0 then img else .var (i - 1)

/-- Haskell `indcFst`: induction on the first variable.  One case per constructor, with the
induction hypotheses (one per recursive field) as lemmas over the other variables. -/
def indcFst (cx : PCtx) (c : Conj) :
    Option (Comment × List (Comment × List Conj × Conj)) :=
  match c.aff.ctx, c.names with
  | ty :: tys, v :: vs =>
    match cx.data.find? (·.name == ty) with
    | none => none
    | some d =>
      let used := c.names ++ namesUsed c.names c.aff.lhs ++ namesUsed c.names c.aff.rhs ++
        cx.env.map (·.1) ++ cx.defNames
      let cases := d.ctors.map fun (con, fs) =>
        let fnames := freshN used fs.length
        let fields := fnames.map Term.const
        let sub := fun (img : Term) =>
          (⟨tys, dropFirstVar img c.aff.lhs, dropFirstVar img c.aff.rhs⟩ : Affirm)
        let goal : Conj := { names := vs, aff := sub ((Term.con con).mkApp fields) }
        let hs : List Conj := ((fnames.zip fs).filter (·.2 == d.name)).map fun (k, _) =>
          { names := vs, aff := sub (.const k) }
        (Comment.caso v, hs, goal)
      some (.induction v, cases)
  | _, _ => none

/-- Haskell `mainTactic`, with `fuel` as the bound on the depth of the tree built (the
Haskell tree is lazy and infinite; `giveUp` cuts it anyway). -/
def mainTactic (cx : PCtx) : Nat → HRec → Conj → Proof
  | 0, _, _ => .fail
  | fuel + 1, rec, c =>
    if c.aff.lhs == c.aff.rhs then .step c .triv .done
    else
      match bothSides (computeDontEndInCas cx.env) c with
      | some (cm, a) => .step c cm (mainTactic cx fuel rec a)
      | none =>
        match applyRecH rec c with
        | some (cm, a) => .step c cm (mainTactic cx fuel rec a)
        | none =>
          match indcFst cx c with
          | some (cm, cases) =>
            .ind c cm (cases.map fun (cc, hs, t) =>
              (cc, hs, mainTactic cx fuel (rec.addAll cx.env hs) t))
          | none => .step c .noIdea .fail

/-! ### Cutting: cycles and the step budget -/

mutual
  /-- Haskell `cutSingleStepCycles`: a step that returns to the statement of two or three
  steps before is cut. -/
  def cutSingleStepCycles : Proof → Proof
    | .step x c p =>
      match p with
      | .step y k q =>
        match q with
        | .step u _ _ =>
          if x == u then .step x c (.step y k (.step u .loop .fail))
          else .step x c (cutSingleStepCycles p)
        | _ => if x == y then .step x c (.step y k .fail) else .step x c (cutSingleStepCycles p)
      | _ => .step x c (cutSingleStepCycles p)
    | .ind x s xs => .ind x s (cutCases xs)
    | a => a

  def cutCases : List (Comment × List Conj × Proof) → List (Comment × List Conj × Proof)
    | [] => []
    | (c, hs, t) :: r => (c, hs, cutSingleStepCycles t) :: cutCases r
end

mutual
  /-- Haskell `giveUp n`: `none` if the proof fits in `n` steps (nothing to cut), else the
  proof with the excess replaced by `fail`.  The budget is shared by the cases of an
  induction. -/
  def giveUp : Nat → Proof → Option Proof
    | _, .done => none
    | _, .fail => some .fail
    | n, .step x s p => if n == 0 then some .fail else (giveUp (n - 1) p).map fun r => Proof.step x s r
    | n, .ind x s cs => if n == 0 then some .fail else (giveUpCases (n - 1) cs).map fun r => Proof.ind x s r

  def giveUpCases : Nat → List (Comment × List Conj × Proof) →
      Option (List (Comment × List Conj × Proof))
    | _, [] => some []
    | n, (c, hs, t) :: xs =>
      match giveUp n t with
      | some a => some [(c, hs, a)]
      | none =>
        match giveUpCases (n - 1 - t.size) xs with
        | none => none
        | some [] => none
        | some (a :: as) => some ((c, hs, t) :: a :: as)
end

/-- Haskell `prove n`: build the proof, cut cycles, cut to the budget. -/
def prove (cx : PCtx) (n : Nat) (rec : HRec) (c : Conj) : Proof :=
  let p := cutSingleStepCycles (mainTactic cx (n + 1) rec c)
  (giveUp n p).getD p

/-! ## `provell` -/

/-- One batch of `provell`: the conjectures tried (those no stored lemma rewrites) with
their proofs, and the first complete one. -/
structure BatchResult where
  tried : List (Conj × Proof)
  chosen : Option Proof

/-- Haskell `provell`, keeping what was tried. -/
def provell (cx : PCtx) (n : Nat) : HRec → List (List Conj) → List BatchResult
  | _, [] => []
  | rec, b :: bs =>
    let cands := b.filter fun c => (applyRecH rec c).isNone
    let tried := cands.map fun c => (c, prove cx n rec c)
    match tried.find? (·.2.complete) with
    | none => ⟨tried, none⟩ :: provell cx n rec bs
    | some (_, p) =>
      let rec' := match p.head with
        | some h => rec.addAll cx.env [h]
        | none => rec
      ⟨tried, some p⟩ :: provell cx n rec' bs

end MM
