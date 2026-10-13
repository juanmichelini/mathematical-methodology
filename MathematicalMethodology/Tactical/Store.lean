import MathematicalMethodology.Tactical.Cert

/-!
# Tactical level: the lemma store (untrusted)

Port of the bookkeeping in `juanmichelini/foundations` `code/Prove.hs` that
`mainTactic` needs: how big a term is (`fund`), what it depends on
(`dependencies`), how two sides of a lemma compare (`compareDep`, `floatsDep`,
`floatsEnv`, `masOrd`), and the store of proven lemmas (`Rec`, `Rec.add`).

Nothing here is trusted: it only decides which lemma to *try*.  Whatever the search
builds from it is re-checked by `Cert.check`.  This file must not be imported by
`Cert.lean` or by the operational level.

## Differences from the Haskell code

* Variables are de Bruijn indices, so `Atom.var` carries an index, not a name.  The
  Haskell code compares variable names to order atoms; here the order is
  `var < const < con`, then by index/name.  Any fixed total order serves (it is only
  used to make permutation rewriting terminate), but exact tie-breaks can differ from
  Haskell where names matter.
* Defined functions are `const f` atoms (in Haskell they are `Var` atoms found in `env`).
* `dependencies` is bounded by the size of the environment, so mutually recursive
  definitions cannot make it loop (Haskell would loop).
* `Rec.flod` and `Rec.floe` exist, as in Haskell, but nothing fills them: Haskell's
  `addAffirm` only fills `simp`, `reor` and `basu`.
-/

namespace MM

/-! ## Atoms -/

/-- The atoms of a term: free variables, constructors and defined functions. -/
inductive Atom where
  | var   (i : Nat)
  | const (f : String)
  | con   (c : String)
  deriving DecidableEq, Repr

def Atom.cmp : Atom → Atom → Ordering
  | .var i, .var j => compare i j
  | .var _, _ => .lt
  | .const _, .var _ => .gt
  | .const f, .const g => compare f g
  | .const _, .con _ => .lt
  | .con _, .con _ => .eq
  | .con _, _ => .gt

instance : Ord Atom := ⟨Atom.cmp⟩

/-! ## Atoms, heights and arguments of a term -/

mutual
  /-- Free atoms (Haskell `termToFreeAtm`/`termToFreeAtmCas`).  `d` is the number of
  enclosing binders: variables below it are bound and dropped, the others are shifted
  down.  With `withCas`, each `case` alternative also contributes its constructor. -/
  def Term.freeAtoms (withCas : Bool) (d : Nat) : Term → List Atom
    | .var i => if i < d then [] else [.var (i - d)]
    | .con c => [.con c]
    | .const f => [.const f]
    | .app f a => f.freeAtoms withCas d ++ a.freeAtoms withCas d
    | .abs b => b.freeAtoms withCas (d + 1)
    | .cas s alts => s.freeAtoms withCas d ++ alts.freeAtoms withCas d

  def Alts.freeAtoms (withCas : Bool) (d : Nat) : Alts → List Atom
    | .nil => []
    | .alt c k b rest =>
      (if withCas then [Atom.con c] else []) ++ b.freeAtoms withCas (d + k) ++
        rest.freeAtoms withCas d
end

mutual
  /-- All atoms, binders ignored (Haskell `termToAtm`).  Meant for binder-free lemma
  statements, where variable indices mean the same everywhere. -/
  def Term.atoms : Term → List Atom
    | .var i => [.var i]
    | .con c => [.con c]
    | .const f => [.const f]
    | .app f a => f.atoms ++ a.atoms
    | .abs b => b.atoms
    | .cas s alts => s.atoms ++ alts.atoms

  def Alts.atoms : Alts → List Atom
    | .nil => []
    | .alt _ _ b rest => b.atoms ++ rest.atoms
end

mutual
  /-- Height of each atom (Haskell `alturas`). -/
  def Term.heights : Term → List Nat
    | .var _ => [0]
    | .con _ => [0]
    | .const _ => [0]
    | .app f a => (f.heights ++ a.heights).map (· + 1)
    | .abs b => b.heights.map (· + 1)
    | .cas s alts => (s.heights ++ alts.heights).map (· + 1)

  def Alts.heights : Alts → List Nat
    | .nil => []
    | .alt _ _ b rest => b.heights ++ rest.heights
end

mutual
  /-- Atoms in argument position (Haskell `termToAtmArgs`): the head atom of an
  application is skipped. -/
  def Term.argAtoms : Term → List Atom
    | .var i => [.var i]
    | .con c => [.con c]
    | .const f => [.const f]
    | .app (.var _) y => y.argAtoms
    | .app (.con _) y => y.argAtoms
    | .app (.const _) y => y.argAtoms
    | .app x y => x.argAtoms ++ y.argAtoms
    | .abs b => b.argAtoms
    | .cas s alts => s.argAtoms ++ alts.argAtoms

  def Alts.argAtoms : Alts → List Atom
    | .nil => []
    | .alt _ _ b rest => b.argAtoms ++ rest.argAtoms
end

/-! ## Size and dependencies -/

/-- Number of pattern variables bound by the alternatives. -/
def Alts.patternVars : Alts → Nat
  | .nil => 0
  | .alt _ k _ rest => k + rest.patternVars

mutual
  /-- `fund` with an explicit fuel: unfolding a definition spends one unit and removes
  it from the environment, so `env.length + 1` units always suffice. -/
  def Term.fundF : Nat → Env → Term → Nat
    | 0, _, _ => 0
    | _ + 1, _, .var _ => 0
    | _ + 1, _, .con _ => 1
    | n + 1, env, .const f =>
      match env.lookup f with
      | none => 0
      | some body => Term.fundF n (env.filter (·.1 ≠ f)) body
    | n + 1, env, .app x y =>
      let fx := Term.fundF (n + 1) env x
      let fy := Term.fundF (n + 1) env y
      if fx > fy then fx + fy else fy
    | n + 1, env, .abs b => 1 + Term.fundF (n + 1) env b
    | n + 1, env, .cas s alts =>
      alts.patternVars + max (Term.fundF (n + 1) env s) (Alts.maxBodyF (n + 1) env alts)
  termination_by n _ t => (n, sizeOf t)

  def Alts.maxBodyF : Nat → Env → Alts → Nat
    | 0, _, _ => 0
    | _ + 1, _, .nil => 0
    | n + 1, env, .alt _ _ b rest =>
      max (Term.fundF (n + 1) env b) (Alts.maxBodyF (n + 1) env rest)
  termination_by n _ a => (n, sizeOf a)
end

/-- Haskell `fund`: a measure of how much a term "contains", unfolding each definition
in `env` at most once along any path. -/
def Term.fund (env : Env) (t : Term) : Nat := Term.fundF (env.length + 1) env t

/-! ## Dependencies -/

/-- Dependencies of an atom: itself and, if it is a defined function, everything its
definition mentions (transitively).  Bounded by the size of the environment. -/
def depsAtom (env : Env) : Nat → Atom → List Atom
  | 0, a => [a]
  | fuel + 1, a =>
    a :: match a with
      | .const f =>
        match env.lookup f with
        | none => []
        | some k =>
          (((k.freeAtoms true 0).filter (· ≠ a)).flatMap (depsAtom env fuel)).eraseDups
      | _ => []

/-- Haskell `dependencies`. -/
def dependencies (env : Env) (t : Term) : List Atom :=
  ((t.freeAtoms true 0).eraseDups.flatMap (depsAtom env (env.length + 1))).eraseDups

/-- Haskell `idependencies`: one level, without constructors of `case` alternatives. -/
def idependencies (env : Env) (t : Term) : List Atom :=
  let one : Atom → List Atom := fun a =>
    match a with
    | .const f =>
      match env.lookup f with
      | none => []
      | some k => ((k.freeAtoms false 0).filter (· ≠ a)).eraseDups
    | _ => []
  ((t.freeAtoms false 0).eraseDups.flatMap one).eraseDups

/-! ## Comparing the two sides of a lemma -/

def Affirm.flip (a : Affirm) : Affirm := { a with lhs := a.rhs, rhs := a.lhs }

private def firstNonEq (os : List Ordering) : Option Ordering :=
  (os.filter (· ≠ .eq)).head?

/-- Haskell `compareDep`: does the left side depend on everything the right one does? -/
def compareDep (env : Env) (a : Affirm) : Option Ordering :=
  let bd := dependencies env a.lhs
  let cd := dependencies env a.rhs
  match cd.all (bd.contains ·), bd.all (cd.contains ·) with
  | true, true => some .eq
  | true, false => some .gt
  | false, true => some .lt
  | false, false => none

/-- Haskell `simplifies`. -/
def simplifies (env : Env) (a : Affirm) : Bool := compareDep env a == some .gt

/-- Haskell `simplifiesOrd`. -/
def simplifiesOrd (env : Env) (a b : Affirm) : Ordering :=
  let n (t : Term) : Int := (dependencies env t).length
  compare (n b.lhs - n b.rhs) (n a.lhs - n a.rhs)

/-- Number of dependencies of each atom of a term (Haskell `map (length . dependenciesAtm)`). -/
def atomOrders (env : Env) (t : Term) : List Nat :=
  t.atoms.map fun a => (depsAtom env (env.length + 1) a).length

/-- Haskell `floatsDep`. -/
def floatsDep (env : Env) (a : Affirm) : Bool :=
  let bd := dependencies env a.lhs
  let cd := dependencies env a.rhs
  cd.all (bd.contains ·) &&
    firstNonEq ((atomOrders env a.lhs).zipWith compare (atomOrders env a.rhs)) == some .gt

/-- Haskell `floatsDepOrd`. -/
def floatsDepOrd (env : Env) (a b : Affirm) : Ordering :=
  let ord (x : Affirm) : List Ordering :=
    (atomOrders env x.lhs).zipWith compare (atomOrders env x.rhs)
  (firstNonEq ((ord a).zipWith compare (ord b))).getD .eq

/-- Position of a defined function in the environment (Haskell `ordEnv`). -/
def envIndex (env : Env) : Atom → Option Nat
  | .const f => env.findIdx? (·.1 = f) |>.filter (· < env.length)
  | _ => none

def ordEnv (env : Env) (x y : Atom) : Ordering :=
  match envIndex env x, envIndex env y with
  | none, none => .eq
  | some _, none => .gt
  | none, some _ => .lt
  | some i, some j => compare i j

/-- Haskell `floatsEnv`. -/
def floatsEnv (env : Env) (a : Affirm) : Bool :=
  firstNonEq (a.lhs.atoms.zipWith (ordEnv env) a.rhs.atoms) == some .gt

/-- Haskell `masOrd`: a total preorder on terms used to orient permutation lemmas. -/
def masOrd (t1 t2 : Term) : Ordering :=
  match firstNonEq (t1.argAtoms.zipWith compare t2.argAtoms) with
  | some o => o
  | none => (firstNonEq (t1.heights.zipWith compare t2.heights)).getD .eq

/-- The two sides have the same atoms, in some order (Haskell `permuta`). -/
def permuta (a : Affirm) : Bool :=
  let sort (l : List Atom) := l.mergeSort fun x y => compare x y != .gt
  sort a.lhs.atoms == sort a.rhs.atoms

def soloPermuta (a : Affirm) : Bool :=
  let sort (l : List Atom) := l.mergeSort fun x y => compare x y != .gt
  a.lhs.atoms.head? == a.rhs.atoms.head? && sort a.lhs.atoms == sort a.rhs.atoms

inductive FlowAffirm | swap | float | reord
  deriving DecidableEq, Repr

/-- Haskell `toJera`. -/
def toJera (a : Affirm) : Option FlowAffirm :=
  let xs := a.lhs.atoms.eraseDups
  let ys := a.rhs.atoms.eraseDups
  let int := xs.filter (ys.contains ·)
  let sxs := xs.filter (!int.contains ·)
  let sys := ys.filter (!int.contains ·)
  if sxs.isEmpty && sys.isEmpty then
    if xs.head? == ys.head? then some .reord else some .float
  else some .swap

/-! ## The store of proven lemmas -/

/-- Haskell `Rec`.  `flod` and `floe` are never filled by `Rec.add` (as in Haskell). -/
structure Rec where
  simp : List Affirm := []
  flod : List Affirm := []
  floe : List Affirm := []
  reor : List Affirm := []
  basu : List Affirm := []
  todo : List Affirm := []
  deriving Repr

def Rec.empty : Rec := {}

/-- Haskell `insertBy`: insert before the first element that is not smaller. -/
def insertBy {α : Type} (cmp : α → α → Ordering) (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
    match cmp x y with
    | .gt => y :: insertBy cmp x ys
    | _ => x :: y :: ys

/-- Haskell `addAffirm`: a lemma whose left side is bigger (`fund`) rewrites left to
right (`simp`); a smaller one is stored flipped; a permutation lemma goes to `reor` in
both directions; anything else is kept in `basu`. -/
def Rec.add (env : Env) (r : Rec) (l : Affirm) : Rec :=
  let fa := l.lhs.fund env
  let fb := l.rhs.fund env
  let l' := l.flip
  let gap (a : Affirm) : Int := (a.lhs.fund env : Int) - (a.rhs.fund env : Int)
  let compF (a b : Affirm) : Ordering := compare (gap a) (gap b)
  let compSnd (a b : Affirm) : Ordering := masOrd a.rhs b.rhs
  if fa > fb then { r with simp := insertBy compF l r.simp }
  else if fa < fb then { r with simp := insertBy compF l' r.simp }
  else if permuta l then { r with reor := insertBy compSnd l (insertBy compSnd l' r.reor) }
  else { r with basu := l :: r.basu }

def Rec.addAll (env : Env) (r : Rec) (ls : List Affirm) : Rec := ls.foldl (Rec.add env) r

end MM
