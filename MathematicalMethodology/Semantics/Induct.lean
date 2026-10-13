import MathematicalMethodology.Semantics.Rewrite

/-!
# Soundness of induction

The checker's `induct` step is sound: if every constructor case is `Sound`, then the
goal is `Sound`.  The proof is by induction on the value that variable `v` takes.
-/

namespace MM

/-- `g` is proved from `rules` when it holds under every value substitution for which
the rules hold. -/
def Sound (cx : Ctx) (rules : List Rule) (g : Affirm) : Prop :=
  ∀ σ, ValSub cx.data g.ctx σ → (∀ r ∈ rules, RuleHolds cx.env cx.data σ r) →
    Conv cx.env (g.lhs.subst σ) (g.rhs.subst σ)

/-- The substitution for the subgoal of a constructor case: variables below `v` keep
their value, those above `v` shift down, the field variables take the constructor's
arguments. -/
def subSub (v n : Nat) (σ : Nat → Term) (args : List Term) : Nat → Term := fun i =>
  if i < v then σ i else if i < n - 1 then σ (i + 1) else args.getD (i - (n - 1)) (.var 0)

theorem fieldVars_subst (v n : Nat) (hv : v < n) (σ : Nat → Term) (args : List Term) :
    (fieldVars n args.length).map (·.subst (subSub v n σ args)) = args := by
  apply List.ext_getElem
  · simp [fieldVars]
  · intro j h1 h2
    simp only [fieldVars, List.map_map, List.getElem_map, List.getElem_range,
      Function.comp_apply, Term.subst, subSub]
    rw [if_neg (by omega), if_neg (by omega)]
    have : n - 1 + j - (n - 1) = j := by omega
    rw [this, getD_of_lt _ _ h2]

theorem caseSubst_comp (v n : Nat) (hv : v < n) (σ : Nat → Term) (c : String)
    (args : List Term) (hσv : σ v = Term.mkApp (.con c) args) :
    ∀ i, i < n → (caseSubst n v c args.length i).subst (subSub v n σ args) = σ i := by
  intro i hi
  unfold caseSubst closeGap
  by_cases h1 : i < v
  · simp only [if_pos h1, Term.subst, subSub]
  · by_cases h2 : i = v
    · subst h2
      simp only [if_neg h1, if_true]
      rw [Term.mkApp_subst, fieldVars_subst i n hv σ args, hσv]
      rfl
    · simp only [if_neg h1, if_neg h2, Term.subst, subSub]
      rw [if_neg (by omega), if_pos (by omega)]
      congr 1
      omega

theorem induct_claim {cx : Ctx} (g : Affirm) (v : Nat) (d : DataDecl) (rules : List Rule)
    (hvn : v < g.ctx.length)
    (hsc : g.lhs.scoped g.ctx.length = true ∧ g.rhs.scoped g.ctx.length = true)
    (hsub : ∀ p ∈ inductCases g v d rules, Sound cx p.2 p.1)
    (hL : ∀ r ∈ rules, r.tys ≠ [] → ∀ τ, ValSub cx.data r.tys τ →
      Conv cx.env (r.lhs.subst τ) (r.rhs.subst τ)) :
    ∀ (ty : String) (u : Term), IsVal cx.data ty u → g.ctx[v]? = some ty →
      cx.data.find? (·.name = ty) = some d →
      ∀ σ, ValSub cx.data g.ctx σ → σ v = u →
        Conv cx.env (g.lhs.subst σ) (g.rhs.subst σ) := by
  intro ty u hu
  induction hu with
  | opq ty w hnone _ =>
    intro _ hd
    rw [hnone] at hd
    simp at hd
  | ctor ty d' c fields args hfd hmem hlen hargs ih =>
    intro hv hd σ hσ hσv
    have hdd : d' = d := by rw [hd] at hfd; exact (Option.some.inj hfd).symm
    subst hdd
    have hname : d'.name = ty := by simpa using List.find?_some hfd
    have hcase := hsub (inductCase g v d'.name rules (c, fields))
      (List.mem_map.mpr ⟨(c, fields), hmem, rfl⟩)
    let n := g.ctx.length
    let σ' := subSub v n σ args
    have hk : fields.length = args.length := hlen.symm
    -- the new substitution is a value substitution for the subgoal's context
    have hvalsub : ValSub cx.data (g.ctx.eraseIdx v ++ fields) σ' := by
      intro i ty'' hi
      have hlenE : (g.ctx.eraseIdx v).length = n - 1 := List.length_eraseIdx_of_lt hvn
      by_cases hin : i < n - 1
      · rw [List.getElem?_append_left (by omega), List.getElem?_eraseIdx] at hi
        simp only [σ', subSub]
        by_cases hiv : i < v
        · rw [if_pos hiv] at hi ⊢; exact hσ i ty'' hi
        · rw [if_neg hiv] at hi
          rw [if_neg hiv, if_pos hin]
          exact hσ (i + 1) ty'' hi
      · rw [List.getElem?_append_right (by omega), hlenE] at hi
        have hj : i - (n - 1) < fields.length := (List.getElem?_eq_some_iff.mp hi).1
        have e : fields[i - (n - 1)] = ty'' := by
          rw [List.getElem?_eq_getElem hj] at hi; exact Option.some.inj hi
        have := hargs (i - (n - 1)) hj
        rw [getD_of_lt _ _ hj, e] at this
        simp only [σ', subSub]
        rw [if_neg (by omega), if_neg hin, getD_of_lt _ _ (by omega)]
        rw [getD_of_lt _ _ (by omega)] at this
        exact this
    -- rules available in the subgoal hold
    have hrules : ∀ r ∈ (List.range fields.length).filterMap
          (fun j => if fields.getD j "" = d'.name then some (ihRule g v j) else none) ++
          rules.filter (fun r => !r.tys.isEmpty), RuleHolds cx.env cx.data σ' r := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨j, hj, hjr⟩ := List.mem_filterMap.mp hr
        have hjlt : j < fields.length := List.mem_range.mp hj
        by_cases hfj : fields.getD j "" = d'.name
        · rw [if_pos hfj] at hjr
          simp only [Option.some.injEq] at hjr
          subst hjr
          refine ⟨fun _ => ?_, fun hne => absurd rfl hne⟩
          -- the induction hypothesis for field `j`
          let σ'' : Nat → Term := fun i => if i = v then args.getD j (.var 0) else σ i
          have hty : fields.getD j "" = ty := by rw [hfj, hname]
          have hvj : g.ctx[v]? = some (fields.getD j "") := by rw [hty]; exact hv
          have hdj : cx.data.find? (·.name = fields.getD j "") = some d' := by
            rw [hty]; exact hd
          have hσ'' : ValSub cx.data g.ctx σ'' := by
            intro i ty'' hi
            simp only [σ'']
            by_cases hiv : i = v
            · subst hiv
              rw [if_pos rfl]
              have : ty'' = ty := by rw [hv] at hi; exact (Option.some.inj hi).symm
              subst this
              have := hargs j hjlt
              rw [hty] at this
              exact this
            · rw [if_neg hiv]; exact hσ i ty'' hi
          have hmain := ih j hjlt hvj hdj σ'' hσ'' (by simp [σ''])
          have comp : ∀ t : Term, t.scoped n = true →
              (t.subst (closeGap v (.var (n - 1 + j)))).subst σ' = t.subst σ'' := by
            intro t ht
            rw [Term.subst_subst]
            apply Term.subst_congr (n := n) _ t ht
            intro i hi
            simp only [closeGap, σ'', σ']
            by_cases h1 : i < v
            · rw [if_pos h1, if_neg (by omega)]
              simp only [Term.subst, subSub]
              rw [if_pos h1]
            · by_cases h2 : i = v
              · subst h2
                rw [if_neg h1, if_pos rfl, if_pos rfl]
                simp only [Term.subst, subSub]
                rw [if_neg (by omega), if_neg (by omega)]
                congr 1
                omega
              · rw [if_neg h1, if_neg h2, if_neg h2]
                simp only [Term.subst, subSub]
                rw [if_neg (by omega), if_pos (by omega)]
                congr 1
                omega
          simp only [ihRule]
          rw [comp _ hsc.1, comp _ hsc.2]
          exact hmain
        · rw [if_neg hfj] at hjr; simp at hjr
      · obtain ⟨hrm, hne⟩ := List.mem_filter.mp hr
        have hne' : r.tys ≠ [] := by
          intro e; rw [e] at hne; simp at hne
        exact ⟨fun e => absurd e hne', fun _ τ hτ => hL r hrm hne' τ hτ⟩
    have hmain := hcase σ' hvalsub hrules
    have e1 : ∀ t : Term, t.scoped n = true →
        (t.subst (caseSubst n v c fields.length)).subst σ' = t.subst σ := by
      intro t ht
      rw [Term.subst_subst]
      apply Term.subst_congr (n := n) _ t ht
      intro i hi
      have := caseSubst_comp v n hvn σ c args (hσv.trans rfl) i hi
      rw [hk]; exact this
    simp only [inductCase] at hmain
    rw [e1 _ hsc.1, e1 _ hsc.2] at hmain
    exact hmain

theorem induct_sound {cx : Ctx} (g : Affirm) (v : Nat) (ty : String) (d : DataDecl)
    (rules : List Rule) (hv : g.ctx[v]? = some ty) (hd : cx.data.find? (·.name = ty) = some d)
    (hsc : g.lhs.scoped g.ctx.length = true ∧ g.rhs.scoped g.ctx.length = true)
    (hsub : ∀ p ∈ inductCases g v d rules, Sound cx p.2 p.1) : Sound cx rules g := by
  intro σ hσ hr
  have hvn : v < g.ctx.length := (List.getElem?_eq_some_iff.mp hv).1
  exact induct_claim g v d rules hvn hsc hsub
    (fun r hm hne => (hr r hm).2 hne) ty (σ v) (hσ v ty hv) hv hd σ hσ rfl

end MM
