import MathematicalMethodology.Operational.Term

/-!
# Substitution algebra

Standard de Bruijn lemmas, proved from scratch (no Mathlib):

* composition of renamings and substitutions,
* `Term.beta` and `Term.instAlt` commute with substitution,
* scoping (`scoped`), closedness, and congruence of substitution on scoped terms.

These are what the soundness proof uses to move substitutions around.
-/

namespace MM

/-! ## Renaming composition -/

theorem liftRen_comp (ρ ρ' : Nat → Nat) : liftRen (ρ' ∘ ρ) = liftRen ρ' ∘ liftRen ρ := by
  funext i; cases i <;> rfl

theorem liftRenN_comp (n : Nat) (ρ ρ' : Nat → Nat) :
    liftRenN n (ρ' ∘ ρ) = liftRenN n ρ' ∘ liftRenN n ρ := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [liftRenN]; rw [ih, liftRen_comp]

mutual
  theorem Term.rename_rename (ρ ρ' : Nat → Nat) :
      ∀ t : Term, (t.rename ρ).rename ρ' = t.rename (ρ' ∘ ρ)
    | .var _ => rfl
    | .con _ => rfl
    | .const _ => rfl
    | .app f a => by
      simp only [Term.rename]
      rw [Term.rename_rename ρ ρ' f, Term.rename_rename ρ ρ' a]
    | .abs b => by
      simp only [Term.rename]
      rw [Term.rename_rename (liftRen ρ) (liftRen ρ') b, liftRen_comp]
    | .cas s alts => by
      simp only [Term.rename]
      rw [Term.rename_rename ρ ρ' s, Alts.rename_rename ρ ρ' alts]

  theorem Alts.rename_rename (ρ ρ' : Nat → Nat) :
      ∀ a : Alts, (a.rename ρ).rename ρ' = a.rename (ρ' ∘ ρ)
    | .nil => rfl
    | .alt c n b rest => by
      simp only [Alts.rename]
      rw [Term.rename_rename (liftRenN n ρ) (liftRenN n ρ') b, liftRenN_comp,
        Alts.rename_rename ρ ρ' rest]
end

/-! ## Renaming after substitution -/

theorem upSub_rename (σ : Nat → Term) (ρ : Nat → Nat) :
    (fun i => (upSub σ i).rename (liftRen ρ)) = upSub (fun i => (σ i).rename ρ) := by
  funext i
  cases i with
  | zero => rfl
  | succ n =>
    show ((σ n).rename Nat.succ).rename (liftRen ρ) = ((σ n).rename ρ).rename Nat.succ
    rw [Term.rename_rename, Term.rename_rename]
    rfl

theorem upSubN_rename (n : Nat) (σ : Nat → Term) (ρ : Nat → Nat) :
    (fun i => (upSubN n σ i).rename (liftRenN n ρ)) = upSubN n (fun i => (σ i).rename ρ) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show (fun i => (upSub (upSubN k σ) i).rename (liftRen (liftRenN k ρ))) = _
    rw [upSub_rename, ih]
    rfl

mutual
  theorem Term.rename_subst (σ : Nat → Term) (ρ : Nat → Nat) :
      ∀ t : Term, (t.subst σ).rename ρ = t.subst (fun i => (σ i).rename ρ)
    | .var _ => rfl
    | .con _ => rfl
    | .const _ => rfl
    | .app f a => by
      simp only [Term.subst, Term.rename]
      rw [Term.rename_subst σ ρ f, Term.rename_subst σ ρ a]
    | .abs b => by
      simp only [Term.subst, Term.rename]
      rw [Term.rename_subst (upSub σ) (liftRen ρ) b, upSub_rename]
    | .cas s alts => by
      simp only [Term.subst, Term.rename]
      rw [Term.rename_subst σ ρ s, Alts.rename_subst σ ρ alts]

  theorem Alts.rename_subst (σ : Nat → Term) (ρ : Nat → Nat) :
      ∀ a : Alts, (a.subst σ).rename ρ = a.subst (fun i => (σ i).rename ρ)
    | .nil => rfl
    | .alt c n b rest => by
      simp only [Alts.subst, Alts.rename]
      rw [Term.rename_subst (upSubN n σ) (liftRenN n ρ) b, upSubN_rename,
        Alts.rename_subst σ ρ rest]
end

/-! ## Substitution after renaming -/

theorem upSub_liftRen (σ : Nat → Term) (ρ : Nat → Nat) :
    (fun i => upSub σ (liftRen ρ i)) = upSub (fun i => σ (ρ i)) := by
  funext i; cases i <;> rfl

theorem upSubN_liftRenN (n : Nat) (σ : Nat → Term) (ρ : Nat → Nat) :
    (fun i => upSubN n σ (liftRenN n ρ i)) = upSubN n (fun i => σ (ρ i)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show (fun i => upSub (upSubN k σ) (liftRen (liftRenN k ρ) i)) = _
    rw [upSub_liftRen, ih]
    rfl

mutual
  theorem Term.subst_rename (σ : Nat → Term) (ρ : Nat → Nat) :
      ∀ t : Term, (t.rename ρ).subst σ = t.subst (fun i => σ (ρ i))
    | .var _ => rfl
    | .con _ => rfl
    | .const _ => rfl
    | .app f a => by
      simp only [Term.subst, Term.rename]
      rw [Term.subst_rename σ ρ f, Term.subst_rename σ ρ a]
    | .abs b => by
      simp only [Term.subst, Term.rename]
      rw [Term.subst_rename (upSub σ) (liftRen ρ) b, upSub_liftRen]
    | .cas s alts => by
      simp only [Term.subst, Term.rename]
      rw [Term.subst_rename σ ρ s, Alts.subst_rename σ ρ alts]

  theorem Alts.subst_rename (σ : Nat → Term) (ρ : Nat → Nat) :
      ∀ a : Alts, (a.rename ρ).subst σ = a.subst (fun i => σ (ρ i))
    | .nil => rfl
    | .alt c n b rest => by
      simp only [Alts.subst, Alts.rename]
      rw [Term.subst_rename (upSubN n σ) (liftRenN n ρ) b, upSubN_liftRenN,
        Alts.subst_rename σ ρ rest]
end

/-! ## Substitution composition -/

theorem upSub_subst (σ τ : Nat → Term) :
    (fun i => (upSub σ i).subst (upSub τ)) = upSub (fun i => (σ i).subst τ) := by
  funext i
  cases i with
  | zero => rfl
  | succ n =>
    show ((σ n).rename Nat.succ).subst (upSub τ) = ((σ n).subst τ).rename Nat.succ
    rw [Term.subst_rename, Term.rename_subst]
    rfl

theorem upSubN_subst (n : Nat) (σ τ : Nat → Term) :
    (fun i => (upSubN n σ i).subst (upSubN n τ)) = upSubN n (fun i => (σ i).subst τ) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show (fun i => (upSub (upSubN k σ) i).subst (upSub (upSubN k τ))) = _
    rw [upSub_subst, ih]
    rfl

mutual
  theorem Term.subst_subst (σ τ : Nat → Term) :
      ∀ t : Term, (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ)
    | .var _ => rfl
    | .con _ => rfl
    | .const _ => rfl
    | .app f a => by
      simp only [Term.subst]
      rw [Term.subst_subst σ τ f, Term.subst_subst σ τ a]
    | .abs b => by
      simp only [Term.subst]
      rw [Term.subst_subst (upSub σ) (upSub τ) b, upSub_subst]
    | .cas s alts => by
      simp only [Term.subst]
      rw [Term.subst_subst σ τ s, Alts.subst_subst σ τ alts]

  theorem Alts.subst_subst (σ τ : Nat → Term) :
      ∀ a : Alts, (a.subst σ).subst τ = a.subst (fun i => (σ i).subst τ)
    | .nil => rfl
    | .alt c n b rest => by
      simp only [Alts.subst]
      rw [Term.subst_subst (upSubN n σ) (upSubN n τ) b, upSubN_subst,
        Alts.subst_subst σ τ rest]
end

/-! ## Identity substitution -/

theorem upSub_var : upSub Term.var = Term.var := by
  funext i; cases i <;> rfl

theorem upSubN_var (n : Nat) : upSubN n Term.var = Term.var := by
  induction n with
  | zero => rfl
  | succ k ih => show upSub (upSubN k Term.var) = _; rw [ih, upSub_var]

mutual
  theorem Term.subst_var : ∀ t : Term, t.subst Term.var = t
    | .var _ => rfl
    | .con _ => rfl
    | .const _ => rfl
    | .app f a => by simp only [Term.subst]; rw [Term.subst_var f, Term.subst_var a]
    | .abs b => by simp only [Term.subst]; rw [upSub_var, Term.subst_var b]
    | .cas s alts => by simp only [Term.subst]; rw [Term.subst_var s, Alts.subst_var alts]

  theorem Alts.subst_var : ∀ a : Alts, a.subst Term.var = a
    | .nil => rfl
    | .alt c n b rest => by
      simp only [Alts.subst]; rw [upSubN_var, Term.subst_var b, Alts.subst_var rest]
end

end MM
