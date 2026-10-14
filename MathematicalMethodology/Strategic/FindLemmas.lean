import MathematicalMethodology.Strategic.Conjecture
import MathematicalMethodology.Tactical.Prove
import MathematicalMethodology.Tactical.Search

/-!
# Finding lemmas for a function

Port of `findlemas` of foundations `Propose.hs`: generate the batches of conjectures of a
function (`plemas`, with the lemmas known so far filtering what is proposed) and try to prove
them, batch by batch, with the tactic search of `Tactical/Prove.lean` (`provell`): the first
conjecture of a batch that is proven becomes a lemma for everything after it.

**Untrusted.**  A lemma found here is a claim; `Cert.check` decides what counts as checked.
-/

namespace MM.Strategic

open MM

/-! ## The search context for a strategic environment -/

/-- Data declarations in the checker's format: field types are the printed types. -/
def dataDecls (ds : List DatasH) : List DataDecl :=
  ds.map fun (n, cs) => { name := n, ctors := cs.map fun (c, fs) => (c, fs.map Ty.pp) }

mutual
  def maxAltArity : Term → Nat
    | .app f a => max (maxAltArity f) (maxAltArity a)
    | .abs b => maxAltArity b
    | .cas s alts => max (maxAltArity s) (altsMaxArity alts)
    | _ => 0
  def altsMaxArity : Alts → Nat
    | .nil => 0
    | .alt _ n b rest => max (max n (maxAltArity b)) (altsMaxArity rest)
end

/-- The variable names (Haskell `usedVars`) of a generated definition as the enumeration
names it (see `Strategic/Show.lean`): its parameters and the fields and functions it
mentions.  Fresh names for induction fields avoid them. -/
def defNamesOf (t : Term) : List String :=
  let k := funArity t
  let occ := (termAtoms k 0 (funBody t)).filterMap fun
    | .param i => some (letter (k - 1 - i))
    | .field j => some (letter (k + j))
    | .const f => some f
    | .con _ => none
  ((List.range k).map (fun i => letter (k - 1 - i)) ++ occ).eraseDups

/-- The search context: definitions, data types, and the names the definitions use. -/
def mkPCtx (env : Env) (ds : List DatasH) (used : List String) : PCtx :=
  { env := env, data := dataDecls ds, defNames := used.eraseDups }

/-- The lemma store as a filter for new conjectures (Haskell `applyRecT [] rec`). -/
def rejectWith (rec : HRec) : Reject := fun names t => applyRecT rec names t

/-- Haskell `findlemas`: the batches of conjectures for `v` (filtered by the lemmas already
known), proven in order with budget `n`. -/
def findlemas (cx : PCtx) (tenv : TEnv) (n : Nat) (rec : HRec) (v : String) :
    List BatchResult :=
  provell cx n rec (plemas (rejectWith rec) cx.env tenv v)

/-- The lemmas found (the statements of the chosen proofs). -/
def BatchResult.lemma? (b : BatchResult) : Option Conj := b.chosen.bind Proof.head

def lemmasOf (bs : List BatchResult) : List Conj := bs.filterMap BatchResult.lemma?

end MM.Strategic

namespace MM.Strategic

open MM

/-- First-order signatures of the defined functions: argument types and result. -/
def signatures (tenv : TEnv) : List (String × List String × String) :=
  tenv.filterMap fun (t, ty) =>
    match t with
    | .const f =>
      let (ps, r) := ty.parsAndRet
      some (f, ps.map Ty.pp, r.pp)
    | _ => none

/-- The checker's context for a strategic environment. -/
def mkCtx (env : Env) (ds : List DatasH) (tenv : TEnv) : Ctx :=
  { env := env, data := dataDecls ds, sigs := signatures tenv }

/-- Try to certify lemmas found by the Haskell-style search: with the checker's own
Cert-producing search (rigid induction hypotheses), prove them in order, each proven one
becoming a rule for the next; the certificate is re-checked by `Cert.check`.  Returns, for
each lemma, whether a certificate was found *and* accepted. -/
def certify (cx : Ctx) (fuel : Nat) : List Rule → List Conj → List Bool
  | _, [] => []
  | rules, l :: ls =>
    match search cx rules fuel l.aff with
    | some c =>
      let ok := match c.check cx rules l.aff with | .ok () => true | .error _ => false
      ok :: certify cx fuel (rules ++ [l.aff.toRule]) ls
    | none => false :: certify cx fuel (rules ++ [l.aff.toRule]) ls

end MM.Strategic
