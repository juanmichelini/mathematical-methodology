import MathematicalMethodology.Semantics.Val

/-!
# Soundness of matching and rewriting

* `matchFO` / `instFO` produce a binding `b` with `lhs = pattern.subst (get b)`.
* A lemma rule applied at a spine position gives a `Conv`-equal term, provided every
  instance of a pattern variable has the declared type (this is what the typed
  check in `Rule.tryRoot` guarantees).
-/

namespace MM

/-- The substitution described by a binding. -/
def Binding.get (b : Binding) (i : Nat) : Term :=
  match b.find? (·.1 = i) with
  | some p => p.2
  | none => .var 0

/-- `b'` keeps every association of `b`. -/
def Binding.Ext (b b' : Binding) : Prop :=
  ∀ i x, b.find? (·.1 = i) = some x → b'.find? (·.1 = i) = some x

theorem Binding.Ext.refl (b : Binding) : b.Ext b := fun _ _ h => h

theorem Binding.Ext.trans {b1 b2 b3 : Binding} (h1 : b1.Ext b2) (h2 : b2.Ext b3) :
    b1.Ext b3 := fun i x h => h2 i x (h1 i x h)

theorem Binding.Ext.cons_none {b : Binding} {i : Nat} (t : Term)
    (h : b.find? (·.1 = i) = none) : b.Ext ((i, t) :: b) := by
  intro j x hx
  by_cases hj : i = j
  · subst hj; rw [h] at hx; simp at hx
  · simp [hj, hx]

theorem Term.instFO_ext {b b' : Binding} (e : b.Ext b') :
    ∀ (p : Term) (u : Term), p.instFO b = some u → p.instFO b' = some u
  | .var i, u, h => by
    cases hf : b.find? (·.1 = i) with
    | none => simp [Term.instFO, hf] at h
    | some q =>
      have := e i q hf
      simp only [Term.instFO, hf, Option.map_some, Option.some.injEq] at h
      simp [Term.instFO, this, h]
  | .con _, _, h => h
  | .const _, _, h => h
  | .abs _, _, h => by simp [Term.instFO] at h
  | .cas _ _, _, h => by simp [Term.instFO] at h
  | .app f a, u, h => by
    simp only [Term.instFO] at h
    cases hf : f.instFO b with
    | none => simp [hf] at h
    | some f' =>
      cases ha : a.instFO b with
      | none => simp [hf, ha] at h
      | some a' =>
        have h' : Term.app f' a' = u := by simpa [hf, ha] using h
        subst h'
        simp [Term.instFO, Term.instFO_ext e f f' hf, Term.instFO_ext e a a' ha]

theorem Term.instFO_subst (b : Binding) :
    ∀ (p : Term) (u : Term), p.instFO b = some u → u = p.subst b.get
  | .var i, u, h => by
    simp only [Term.instFO] at h
    cases hf : b.find? (·.1 = i) with
    | none => simp [hf] at h
    | some q =>
      simp only [hf, Option.map_some, Option.some.injEq] at h
      subst h
      simp [Term.subst, Binding.get, hf]
  | .con _, u, h => by
    simp only [Term.instFO, Option.some.injEq] at h; subst h; rfl
  | .const _, u, h => by
    simp only [Term.instFO, Option.some.injEq] at h; subst h; rfl
  | .abs _, _, h => by simp [Term.instFO] at h
  | .cas _ _, _, h => by simp [Term.instFO] at h
  | .app f a, u, h => by
    simp only [Term.instFO] at h
    cases hf : f.instFO b with
    | none => simp [hf] at h
    | some f' =>
      cases ha : a.instFO b with
      | none => simp [hf, ha] at h
      | some a' =>
        have h' : Term.app f' a' = u := by simpa [hf, ha] using h
        subst h'
        simp only [Term.subst]
        rw [← Term.instFO_subst b f f' hf, ← Term.instFO_subst b a a' ha]

theorem matchFO_sound :
    ∀ (p t : Term) (b b' : Binding), matchFO p t b = some b' →
      p.instFO b' = some t ∧ b.Ext b'
  | .var i, t, b, b', h => by
    simp only [matchFO] at h
    cases hf : b.find? (·.1 = i) with
    | some p0 =>
      obtain ⟨_, t0⟩ := p0
      simp only [hf] at h
      split at h
      · rename_i heq
        simp only [Option.some.injEq] at h
        subst h
        have hp := List.find?_some hf
        simp at hp
        subst hp
        refine ⟨?_, Binding.Ext.refl _⟩
        simp [Term.instFO, hf, heq]
      · simp at h
    | none =>
      simp only [hf, Option.some.injEq] at h
      subst h
      refine ⟨?_, Binding.Ext.cons_none t hf⟩
      simp [Term.instFO]
  | .con c, .con d, b, b', h => by
    simp only [matchFO] at h
    split at h
    · rename_i hcd
      simp only [Option.some.injEq] at h
      subst h; subst hcd
      exact ⟨rfl, Binding.Ext.refl _⟩
    · simp at h
  | .con c, .var _, _, _, h => by simp [matchFO] at h
  | .con c, .const _, _, _, h => by simp [matchFO] at h
  | .con c, .app _ _, _, _, h => by simp [matchFO] at h
  | .con c, .abs _, _, _, h => by simp [matchFO] at h
  | .con c, .cas _ _, _, _, h => by simp [matchFO] at h
  | .const f, .const g, b, b', h => by
    simp only [matchFO] at h
    split at h
    · rename_i hfg
      simp only [Option.some.injEq] at h
      subst h; subst hfg
      exact ⟨rfl, Binding.Ext.refl _⟩
    · simp at h
  | .const f, .var _, _, _, h => by simp [matchFO] at h
  | .const f, .con _, _, _, h => by simp [matchFO] at h
  | .const f, .app _ _, _, _, h => by simp [matchFO] at h
  | .const f, .abs _, _, _, h => by simp [matchFO] at h
  | .const f, .cas _ _, _, _, h => by simp [matchFO] at h
  | .app p q, .app s t, b, b', h => by
    simp only [matchFO] at h
    cases h1 : matchFO p s b with
    | none => simp [h1] at h
    | some b1 =>
      cases h2 : matchFO q t b1 with
      | none => simp [h1, h2] at h
      | some b2 =>
        have h' : b2 = b' := by simpa [h1, h2] using h
        subst h'
        obtain ⟨ip, e1⟩ := matchFO_sound p s b b1 h1
        obtain ⟨iq, e2⟩ := matchFO_sound q t b1 b2 h2
        refine ⟨?_, e1.trans e2⟩
        have ip' := Term.instFO_ext e2 p s ip
        simp [Term.instFO, ip', iq]
  | .app _ _, .var _, _, _, h => by simp [matchFO] at h
  | .app _ _, .con _, _, _, h => by simp [matchFO] at h
  | .app _ _, .const _, _, _, h => by simp [matchFO] at h
  | .app _ _, .abs _, _, _, h => by simp [matchFO] at h
  | .app _ _, .cas _ _, _, _, h => by simp [matchFO] at h
  | .abs _, _, _, _, h => by simp [matchFO] at h
  | .cas _ _, _, _, _, h => by simp [matchFO] at h

/-! ## Rules -/

/-- What it means for a rule to hold at the current substitution `σ`: a rigid rule
(`tys = []`) holds for `σ`; a lemma rule holds for all value instances of its
variables. -/
def RuleHolds (env : Env) (data : List DataDecl) (σ : Nat → Term) (r : Rule) : Prop :=
  (r.tys = [] → Conv env (r.lhs.subst σ) (r.rhs.subst σ)) ∧
  (r.tys ≠ [] → ∀ τ, ValSub data r.tys τ → Conv env (r.lhs.subst τ) (r.rhs.subst τ))

theorem RuleHolds.orient {env : Env} {data : List DataDecl} {σ : Nat → Term} {r : Rule}
    (h : RuleHolds env data σ r) (rev : Bool) : RuleHolds env data σ (r.orient rev) := by
  cases rev with
  | false => exact h
  | true =>
    refine ⟨fun e => .symm (h.1 e), fun e τ hτ => .symm (h.2 e τ hτ)⟩

theorem Term.subst_conv_fo {env : Env} {τ τ' : Nat → Term} (h : ∀ i, Conv env (τ i) (τ' i)) :
    ∀ t : Term, t.isFO = true → Conv env (t.subst τ) (t.subst τ')
  | .var i, _ => h i
  | .con _, _ => .refl _
  | .const _, _ => .refl _
  | .app f a, ht => by
    simp only [Term.isFO, Bool.and_eq_true] at ht
    exact .app (Term.subst_conv_fo h f ht.1) (Term.subst_conv_fo h a ht.2)
  | .abs _, ht => by simp [Term.isFO] at ht
  | .cas _ _, ht => by simp [Term.isFO] at ht

/-- A lemma that holds for value instances also holds for instances that merely
denote values, as long as it is first-order. -/
theorem lemma_instance {env : Env} {data : List DataDecl} {r : Rule}
    (hl : r.lhs.isFO = true) (hr : r.rhs.isFO = true)
    (hv : ∀ τ, ValSub data r.tys τ → Conv env (r.lhs.subst τ) (r.rhs.subst τ))
    (τ : Nat → Term) (hden : ∀ i ty, r.tys[i]? = some ty → Denotes env data ty (τ i)) :
    Conv env (r.lhs.subst τ) (r.rhs.subst τ) := by
  have H : ∀ i, ∃ u, Conv env (τ i) u ∧ ∀ ty, r.tys[i]? = some ty → IsVal data ty u := by
    intro i
    cases hi : r.tys[i]? with
    | none => exact ⟨τ i, .refl _, by simp⟩
    | some ty =>
      obtain ⟨_, u, hu, hc⟩ := hden i ty hi
      exact ⟨u, hc, fun ty' h' => by
        simp only [Option.some.injEq] at h'
        subst h'; exact hu⟩
  let τ' : Nat → Term := fun i => Classical.choose (H i)
  have hc : ∀ i, Conv env (τ i) (τ' i) := fun i => (Classical.choose_spec (H i)).1
  have hval : ValSub data r.tys τ' := fun i ty hi => (Classical.choose_spec (H i)).2 ty hi
  exact .trans (Term.subst_conv_fo hc _ hl)
    (.trans (hv τ' hval) (.symm (Term.subst_conv_fo hc _ hr)))

theorem tryRoot_sound {cx : Ctx} (hS : SigSound cx) (hD : DataWF cx.data)
    {ctx : List String} {σ : Nat → Term} (hσ : ValSub cx.data ctx σ) {r : Rule}
    (hr : RuleHolds cx.env cx.data σ r) {t u : Term} (h : r.tryRoot cx ctx t = some u) :
    Conv cx.env (t.subst σ) (u.subst σ) := by
  unfold Rule.tryRoot at h
  by_cases he : r.tys.isEmpty = true
  · rw [if_pos he] at h
    have hnil : r.tys = [] := List.isEmpty_iff.mp he
    by_cases htl : t = r.lhs
    · rw [if_pos htl] at h
      simp only [Option.some.injEq] at h
      subst h; subst htl
      exact hr.1 hnil
    · rw [if_neg htl] at h; simp at h
  · rw [if_neg he] at h
    have hne : r.tys ≠ [] := fun e => he (by simp [e])
    by_cases hfo : (r.lhs.isFO && r.rhs.isFO) = true
    · rw [if_pos hfo] at h
      simp only [Bool.and_eq_true] at hfo
      cases hm : matchFO r.lhs t [] with
      | none => simp [hm] at h
      | some b =>
        simp only [hm] at h
        by_cases hall : (List.range r.tys.length).all (fun i =>
            (b.find? (·.1 = i)).any fun p =>
              decide (cx.typeOf ctx p.2 = some ([], r.tys.getD i ""))) = true
        · rw [if_pos hall] at h
          obtain ⟨hli, _⟩ := matchFO_sound r.lhs t [] b hm
          have ht := Term.instFO_subst b _ _ hli
          have hu := Term.instFO_subst b _ _ h
          have key := lemma_instance (r := r) hfo.1 hfo.2 (hr.2 hne)
            (fun i => (b.get i).subst σ) (by
              intro i ty hi
              have hlt : i < r.tys.length := (List.getElem?_eq_some_iff.mp hi).1
              have hmem := List.all_eq_true.mp hall i (List.mem_range.mpr hlt)
              cases hf : b.find? (·.1 = i) with
              | none => simp [hf] at hmem
              | some q =>
                simp only [hf, Option.any_some, decide_eq_true_eq] at hmem
                have hq : q.1 = i := by simpa using List.find?_some hf
                have hget : b.get i = q.2 := by simp [Binding.get, hf]
                have hty := typeOf_sound hS hD hσ q.2 [] _ hmem
                have : r.tys.getD i "" = ty := by
                  rw [getD_of_lt _ _ hlt]
                  rw [List.getElem?_eq_getElem hlt] at hi
                  exact Option.some.inj hi
                simp only [hget]
                rw [this] at hty
                exact hty)
          rw [ht, hu, Term.subst_subst, Term.subst_subst]
          exact key
        · rw [if_neg hall] at h; simp at h
    · rw [if_neg hfo] at h; simp at h

theorem rewriteFirst_sound {cx : Ctx} (hS : SigSound cx) (hD : DataWF cx.data)
    {ctx : List String} {σ : Nat → Term} (hσ : ValSub cx.data ctx σ) {r : Rule}
    (hr : RuleHolds cx.env cx.data σ r) :
    ∀ (t u : Term), t.rewriteFirst cx ctx r = some u →
      Conv cx.env (t.subst σ) (u.subst σ)
  | .var i, u, h => tryRoot_sound hS hD hσ hr h
  | .con c, u, h => tryRoot_sound hS hD hσ hr h
  | .const f, u, h => tryRoot_sound hS hD hσ hr h
  | .abs b, u, h => tryRoot_sound hS hD hσ hr h
  | .app f a, u, h => by
    simp only [Term.rewriteFirst] at h
    cases hroot : r.tryRoot cx ctx (.app f a) with
    | some u' =>
      simp only [hroot, Option.some.injEq] at h
      subst h
      exact tryRoot_sound hS hD hσ hr hroot
    | none =>
      simp only [hroot] at h
      cases hf : f.rewriteFirst cx ctx r with
      | some f' =>
        simp only [hf, Option.some.injEq] at h
        subst h
        exact .app (rewriteFirst_sound hS hD hσ hr f f' hf) (.refl _)
      | none =>
        simp only [hf] at h
        cases ha : a.rewriteFirst cx ctx r with
        | none => simp [ha] at h
        | some a' =>
          simp only [ha, Option.map_some, Option.some.injEq] at h
          subst h
          exact .app (.refl _) (rewriteFirst_sound hS hD hσ hr a a' ha)
  | .cas s alts, u, h => by
    simp only [Term.rewriteFirst] at h
    cases hroot : r.tryRoot cx ctx (.cas s alts) with
    | some u' =>
      simp only [hroot, Option.some.injEq] at h
      subst h
      exact tryRoot_sound hS hD hσ hr hroot
    | none =>
      simp only [hroot] at h
      cases hs : s.rewriteFirst cx ctx r with
      | none => simp [hs] at h
      | some s' =>
        simp only [hs, Option.map_some, Option.some.injEq] at h
        subst h
        exact .cas _ (rewriteFirst_sound hS hD hσ hr s s' hs)

end MM
