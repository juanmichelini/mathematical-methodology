import MathematicalMethodology.Tactical.Store

/-!
# Tactical level: the tactic search (untrusted)

Port of `mainTactic` from `juanmichelini/foundations` `code/Prove.hs`, producing `Cert`s
instead of `Proof` trees.  At each goal, in order:

1. `triv`: both sides are equal → `refl`;
2. compute both sides (`computeWide`), then start over;
3. apply a stored lemma (`applyRec`): `simp` lemmas, then `flod`, `floe`, then `reor`
   lemmas; each side independently; then start over;
4. induct on the first variable (`indcFst`), searching each case;
5. otherwise fail.

The search is **untrusted**.  It only proposes certificates: it computes every next goal
with the checker's own functions (`computeWide`, `Term.rewriteFirst`, `inductCase`), so the
certificate it returns describes exactly the steps it took, and `Cert.check` re-verifies
them.  A bug here can make the search fail, never make a false statement pass.

## Differences from the Haskell code

* A fuel bound replaces `cutSingleStepCycles`/`giveUp`.
* The `reor` guard of Haskell (`masOrd` of the matched subterm and its rewrite) is applied
  to the whole side, because the checker rewrites at the first matching position and has no
  guard of its own.  Each accepted `reor` step still strictly decreases `masOrd`.
* The checker's rule list is the source of truth: the search rebuilds the store from it at
  each goal (lemmas first, then induction hypotheses, as Haskell adds them), so the rule
  indices in the certificate always match what the checker will see.
-/

namespace MM

def Rule.toAffirm (r : Rule) : Affirm := ⟨r.tys, r.lhs, r.rhs⟩

/-- The store for a goal: the checker's lemma rules first, then its rigid rules (the
induction hypotheses), exactly as Haskell adds them. -/
def buildRec (env : Env) (rules : List Rule) : Rec :=
  let lemmas := rules.filter fun r => !r.tys.isEmpty
  let rigid := rules.filter fun r => r.tys.isEmpty
  Rec.empty.addAll env ((lemmas ++ rigid).map Rule.toAffirm)

/-- Index (and orientation) of the checker rule that states `a`. -/
def findRule (rules : List Rule) (a : Affirm) : Option (Nat × Bool) :=
  let idx := fun (p : Rule → Bool) => (List.range rules.length).find? fun i =>
    match rules[i]? with | some r => p r | none => false
  match idx fun r => r.lhs == a.lhs && r.rhs == a.rhs with
  | some i => some (i, false)
  | none => (idx fun r => r.lhs == a.rhs && r.rhs == a.lhs).map fun i => (i, true)

/-- Try the stored lemmas of one class, in order, on one side: the first lemma that
rewrites somewhere gives the step `(rule index, orientation)` and the new side. -/
def tryLemmas (cx : Ctx) (rules : List Rule) (ctx : List String) (lemmas : List Affirm)
    (guardReor : Bool) (t : Term) : Option (Nat × Bool × Term) :=
  lemmas.findSome? fun a =>
    match findRule rules a with
    | none => none
    | some (i, rev) =>
      match rules[i]? with
      | none => none
      | some r =>
        match t.rewriteFirst cx ctx (r.orient rev) with
        | none => none
        | some t' =>
          if t' = t then none
          else if guardReor && masOrd t t' != .gt then none
          else some (i, rev, t')

/-- One `applyRec` step: for the first class (simp, flod, floe, reor) where some side
rewrites, rewrite both sides that can. -/
def applyRec (cx : Ctx) (rules : List Rule) (g : Affirm) :
    Option (Option (Nat × Bool × Term) × Option (Nat × Bool × Term)) :=
  let rec_ := buildRec cx.env rules
  let classes : List (List Affirm × Bool) :=
    [(rec_.simp, false), (rec_.flod, false), (rec_.floe, false), (rec_.reor, true)]
  classes.findSome? fun (ls, guardReor) =>
    let l := tryLemmas cx rules g.ctx ls guardReor g.lhs
    let r := tryLemmas cx rules g.ctx ls guardReor g.rhs
    if l.isSome || r.isSome then some (l, r) else none

/-- Prefix a certificate with the rewrite step found for one side, if any. -/
def wrapRewrite (s : Side) : Option (Nat × Bool × Term) → Cert → Cert
  | some (i, rev, _), c => Cert.rewrite s i rev c
  | none, c => c

mutual
  /-- Search for a certificate of `g` from `rules`, with a fuel bound. -/
  def search (cx : Ctx) (rules : List Rule) : Nat → Affirm → Option Cert
    | 0, _ => none
    | fuel + 1, g =>
      if g.lhs = g.rhs then some .refl
      else
        let cl := g.lhs.computeWide cx.env computeFuel
        let cr := g.rhs.computeWide cx.env computeFuel
        if cl.isSome || cr.isSome then
          let g' : Affirm := ⟨g.ctx, cl.getD g.lhs, cr.getD g.rhs⟩
          (search cx rules fuel g').map fun c =>
            let c := if cr.isSome then Cert.compute .rhs c else c
            if cl.isSome then Cert.compute .lhs c else c
        else
          match applyRec cx rules g with
          | some (l, r) =>
            let g' : Affirm := ⟨g.ctx, (l.map (·.2.2)).getD g.lhs, (r.map (·.2.2)).getD g.rhs⟩
            (search cx rules fuel g').map fun c =>
              wrapRewrite .lhs l (wrapRewrite .rhs r c)
          | none =>
            match g.ctx[0]? with
            | none => none
            | some ty =>
              match cx.data.find? (·.name = ty) with
              | none => none
              | some d =>
                if g.lhs.scoped g.ctx.length && g.rhs.scoped g.ctx.length then
                  (searchAll cx fuel (inductCases g 0 d rules)).map (Cert.induct 0)
                else none

  /-- Search every subgoal of an induction. -/
  def searchAll (cx : Ctx) : Nat → List (Affirm × List Rule) → Option Certs
    | _, [] => some .nil
    | fuel, (g, rs) :: gs =>
      match search cx rs fuel g, searchAll cx fuel gs with
      | some c, some cs => some (.cons c cs)
      | _, _ => none
end

/-- Default fuel (the Haskell `giveUp` budget is 30 steps, halved at each induction). -/
def searchFuel : Nat := 40

/-- Prove a list of conjectures in order, each proven one becoming a rule for the later
ones (the way `checkDevelopment` and Haskell's `provell` thread lemmas). -/
def searchDevelopment (cx : Ctx) :
    List (String × Affirm) → List Rule → List (String × Affirm × Option Cert)
  | [], _ => []
  | (name, g) :: rest, rules =>
    match search cx rules searchFuel g with
    | some c => (name, g, some c) :: searchDevelopment cx rest (rules ++ [g.toRule])
    | none => (name, g, none) :: searchDevelopment cx rest rules

end MM
