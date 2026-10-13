import MathematicalMethodology.Semantics.Induct

/-!
# Soundness of `Cert.check`

**Theorem (`Cert.check_sound`).**  Let `cx` be a checker context such that

* `EnvClosed cx.env`: every definition is a closed term,
* `SigSound cx`: every declared function signature is right (the function maps values
  of the argument types to something convertible to a value of the result type),
* `DataWF cx.data`: data type names are unique.

If `c.check cx rules g = .ok ()` and every rule in `rules` holds, then for every
substitution sending the variables of `g.ctx` to *values* of their types,
`g.lhs` and `g.rhs` are convertible (`Conv`: delta, beta and case reductions, applied
anywhere, with symmetry and transitivity).

`checkDevelopment_sound` lifts this to whole developments: every accepted lemma holds
for all value instances.

The three assumptions are *not* checked by the checker; see `docs/ROADMAP.md`.
-/

namespace MM

theorem Side.set_ctx (g : Affirm) (s : Side) (t : Term) : (s.set g t).ctx = g.ctx := by
  cases s <;> rfl

/-- Stepping one side by a `Conv`-equal term. -/
theorem sound_step {env : Env} {g : Affirm} {σ : Nat → Term} (s : Side) (t' : Term)
    (h1 : Conv env ((s.get g).subst σ) (t'.subst σ))
    (h2 : Conv env ((s.set g t').lhs.subst σ) ((s.set g t').rhs.subst σ)) :
    Conv env (g.lhs.subst σ) (g.rhs.subst σ) := by
  cases s with
  | lhs => exact .trans h1 h2
  | rhs => exact .trans h2 (.symm h1)

mutual
  theorem Cert.check_sound {cx : Ctx} (hE : EnvClosed cx.env) (hS : SigSound cx)
      (hD : DataWF cx.data) :
      ∀ (c : Cert) (rules : List Rule) (g : Affirm),
        c.check cx rules g = .ok () → Sound cx rules g
    | .refl, rules, g, h => by
      simp only [Cert.check] at h
      split at h
      · rename_i heq
        intro σ _ _
        rw [heq]
        exact .refl _
      · simp at h
    | .compute s rest, rules, g, h => by
      simp only [Cert.check] at h
      cases hc : (s.get g).computeWide cx.env computeFuel with
      | none => simp [hc] at h
      | some t' =>
        simp only [hc] at h
        have ih := Cert.check_sound hE hS hD rest rules (s.set g t') h
        intro σ hσ hr
        refine sound_step s t' ?_ (ih σ (by rw [Side.set_ctx]; exact hσ) hr)
        exact Conv.subst hE (Term.computeWide_sound _ _ _ _ hc) σ
    | .rewrite s i rev rest, rules, g, h => by
      simp only [Cert.check] at h
      cases hr : rules[i]? with
      | none => simp [hr] at h
      | some r =>
        simp only [hr] at h
        cases hrw : (s.get g).rewriteFirst cx g.ctx (r.orient rev) with
        | none => simp [hrw] at h
        | some t' =>
          simp only [hrw] at h
          split at h
          · simp at h
          · have ih := Cert.check_sound hE hS hD rest rules (s.set g t') h
            intro σ hσ hrules
            refine sound_step s t' ?_ (ih σ (by rw [Side.set_ctx]; exact hσ) hrules)
            have hmem : r ∈ rules := List.mem_of_getElem? hr
            exact rewriteFirst_sound hS hD hσ ((hrules r hmem).orient rev) _ _ hrw
    | .induct v cases, rules, g, h => by
      simp only [Cert.check] at h
      cases hv : g.ctx[v]? with
      | none => simp [hv] at h
      | some ty =>
        simp only [hv] at h
        cases hd : cx.data.find? (·.name = ty) with
        | none => simp [hd] at h
        | some d =>
          simp only [hd] at h
          split at h
          · rename_i hsc
            simp only [Bool.and_eq_true] at hsc
            exact induct_sound g v ty d rules hv hd hsc
              (Certs.checkAll_sound hE hS hD cases _ h)
          · simp at h

  theorem Certs.checkAll_sound {cx : Ctx} (hE : EnvClosed cx.env) (hS : SigSound cx)
      (hD : DataWF cx.data) :
      ∀ (cs : Certs) (gs : List (Affirm × List Rule)),
        cs.checkAll cx gs = .ok () → ∀ p ∈ gs, Sound cx p.2 p.1
    | .nil, [], _ => by intro p hp; simp at hp
    | .nil, _ :: _, h => by simp [Certs.checkAll] at h
    | .cons _ _, [], h => by simp [Certs.checkAll] at h
    | .cons c rest, (g, rs) :: gs, h => by
      simp only [Certs.checkAll] at h
      cases h1 : c.check cx rs g with
      | error e => simp [h1, Bind.bind, Except.bind] at h
      | ok u =>
        simp only [h1, Bind.bind, Except.bind] at h
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact Cert.check_sound hE hS hD c rs g h1
        · exact Certs.checkAll_sound hE hS hD rest gs h p hp
end

/-! ## Developments -/

/-- A lemma holds for all value instances of its variables. -/
def LemmaValid (cx : Ctx) (r : Rule) : Prop :=
  ∀ τ, ValSub cx.data r.tys τ → Conv cx.env (r.lhs.subst τ) (r.rhs.subst τ)

theorem LemmaValid.holds {cx : Ctx} {r : Rule} (h : LemmaValid cx r) (σ : Nat → Term) :
    RuleHolds cx.env cx.data σ r :=
  ⟨fun e => h σ (by rw [e]; intro i ty hi; simp at hi), fun _ => h⟩

theorem checkDevelopment_sound {cx : Ctx} (hE : EnvClosed cx.env) (hS : SigSound cx)
    (hD : DataWF cx.data) :
    ∀ (dev : List (String × Affirm × Cert)) (rules rules' : List Rule),
      checkDevelopment cx dev rules = .ok rules' →
      (∀ r ∈ rules, LemmaValid cx r) →
      (∀ r ∈ rules', LemmaValid cx r) ∧ (∀ r ∈ rules, r ∈ rules') ∧
        (∀ e ∈ dev, e.2.1.toRule ∈ rules')
  | [], rules, rules', h, hr => by
    simp only [checkDevelopment, Except.ok.injEq] at h
    subst h
    exact ⟨hr, fun r hm => hm, fun e he => by simp at he⟩
  | (name, g, c) :: rest, rules, rules', h, hr => by
    simp only [checkDevelopment] at h
    cases hc : c.check cx rules g with
    | error e => simp [hc] at h
    | ok u =>
      simp only [hc] at h
      have hs := Cert.check_sound hE hS hD c rules g hc
      have hv : LemmaValid cx g.toRule := by
        intro τ hτ
        exact hs τ hτ (fun r hm => (hr r hm).holds τ)
      obtain ⟨h1, h2, h3⟩ := checkDevelopment_sound hE hS hD rest (rules ++ [g.toRule]) rules' h
        (by
          intro r hm
          rcases List.mem_append.mp hm with hm | hm
          · exact hr r hm
          · simp at hm; subst hm; exact hv)
      refine ⟨h1, fun r hm => h2 r (List.mem_append_left _ hm), ?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact h2 _ (List.mem_append_right _ (by simp))
      · exact h3 e he

/-- **Soundness of a whole development.**  If the checker accepts a development from
no rules, every lemma in it holds for all value instances. -/
theorem checkDevelopment_valid {cx : Ctx} (hE : EnvClosed cx.env) (hS : SigSound cx)
    (hD : DataWF cx.data) (dev : List (String × Affirm × Cert)) (rules' : List Rule)
    (h : checkDevelopment cx dev [] = .ok rules') :
    ∀ e ∈ dev, LemmaValid cx e.2.1.toRule := by
  obtain ⟨h1, _, h3⟩ := checkDevelopment_sound hE hS hD dev [] rules' h
    (fun r hm => by simp at hm)
  exact fun e he => h1 _ (h3 e he)

end MM
