import MathematicalMethodology.Semantics.Subst
import MathematicalMethodology.Operational.Scope

/-!
# Scoping, closedness, and substitution facts

* `Term.scoped n t`: every free variable of `t` is below `n`.
* Substitution only depends on the values of `σ` at free variables (`subst_congr`).
* `beta` and `instAlt` commute with substitution.
-/

namespace MM

/-! ## Scoping and renaming -/

theorem liftRen_lt {n m : Nat} {ρ : Nat → Nat} (h : ∀ i, i < n → ρ i < m) :
    ∀ i, i < n + 1 → liftRen ρ i < m + 1 := by
  intro i hi
  cases i with
  | zero => exact Nat.succ_pos m
  | succ j => exact Nat.succ_lt_succ (h j (Nat.lt_of_succ_lt_succ hi))

theorem liftRenN_lt {n m : Nat} {ρ : Nat → Nat} (h : ∀ i, i < n → ρ i < m) (k : Nat) :
    ∀ i, i < n + k → liftRenN k ρ i < m + k := by
  induction k with
  | zero => exact h
  | succ k ih => exact liftRen_lt ih

mutual
  theorem Term.scoped_rename {ρ : Nat → Nat} {n m : Nat} (h : ∀ i, i < n → ρ i < m) :
      ∀ t : Term, t.scoped n = true → (t.rename ρ).scoped m = true
    | .var i, ht => by
      simp only [Term.scoped, Term.rename, decide_eq_true_eq] at ht ⊢
      exact h i ht
    | .con _, _ => rfl
    | .const _, _ => rfl
    | .app f a, ht => by
      simp only [Term.scoped, Term.rename, Bool.and_eq_true] at ht ⊢
      exact ⟨Term.scoped_rename h f ht.1, Term.scoped_rename h a ht.2⟩
    | .abs b, ht => by
      simp only [Term.scoped, Term.rename] at ht ⊢
      exact Term.scoped_rename (liftRen_lt h) b ht
    | .cas s alts, ht => by
      simp only [Term.scoped, Term.rename, Bool.and_eq_true] at ht ⊢
      exact ⟨Term.scoped_rename h s ht.1, Alts.scoped_rename h alts ht.2⟩

  theorem Alts.scoped_rename {ρ : Nat → Nat} {n m : Nat} (h : ∀ i, i < n → ρ i < m) :
      ∀ a : Alts, a.scoped n = true → (a.rename ρ).scoped m = true
    | .nil, _ => rfl
    | .alt c k b rest, ht => by
      simp only [Alts.scoped, Alts.rename, Bool.and_eq_true] at ht ⊢
      exact ⟨Term.scoped_rename (liftRenN_lt h k) b ht.1, Alts.scoped_rename h rest ht.2⟩
end

/-! ## Scoping and substitution -/

theorem upSub_scoped {σ : Nat → Term} {n m : Nat} (h : ∀ i, i < n → (σ i).scoped m = true) :
    ∀ i, i < n + 1 → (upSub σ i).scoped (m + 1) = true := by
  intro i hi
  cases i with
  | zero => simp [upSub, Term.scoped]
  | succ j =>
    exact Term.scoped_rename (n := m) (m := m + 1)
      (fun i hi => Nat.succ_lt_succ hi) (σ j) (h j (Nat.lt_of_succ_lt_succ hi))

theorem upSubN_scoped {σ : Nat → Term} {n m : Nat} (h : ∀ i, i < n → (σ i).scoped m = true)
    (k : Nat) : ∀ i, i < n + k → (upSubN k σ i).scoped (m + k) = true := by
  induction k with
  | zero => exact h
  | succ k ih => exact upSub_scoped ih

mutual
  theorem Term.scoped_subst {σ : Nat → Term} {n m : Nat}
      (h : ∀ i, i < n → (σ i).scoped m = true) :
      ∀ t : Term, t.scoped n = true → (t.subst σ).scoped m = true
    | .var i, ht => by
      simp only [Term.scoped, decide_eq_true_eq] at ht
      exact h i ht
    | .con _, _ => rfl
    | .const _, _ => rfl
    | .app f a, ht => by
      simp only [Term.scoped, Term.subst, Bool.and_eq_true] at ht ⊢
      exact ⟨Term.scoped_subst h f ht.1, Term.scoped_subst h a ht.2⟩
    | .abs b, ht => by
      simp only [Term.scoped, Term.subst] at ht ⊢
      exact Term.scoped_subst (upSub_scoped h) b ht
    | .cas s alts, ht => by
      simp only [Term.scoped, Term.subst, Bool.and_eq_true] at ht ⊢
      exact ⟨Term.scoped_subst h s ht.1, Alts.scoped_subst h alts ht.2⟩

  theorem Alts.scoped_subst {σ : Nat → Term} {n m : Nat}
      (h : ∀ i, i < n → (σ i).scoped m = true) :
      ∀ a : Alts, a.scoped n = true → (a.subst σ).scoped m = true
    | .nil, _ => rfl
    | .alt c k b rest, ht => by
      simp only [Alts.scoped, Alts.subst, Bool.and_eq_true] at ht ⊢
      exact ⟨Term.scoped_subst (upSubN_scoped h k) b ht.1, Alts.scoped_subst h rest ht.2⟩
end

/-! ## Substitution depends only on free variables -/

theorem upSub_congr {σ σ' : Nat → Term} {n : Nat} (h : ∀ i, i < n → σ i = σ' i) :
    ∀ i, i < n + 1 → upSub σ i = upSub σ' i := by
  intro i hi
  cases i with
  | zero => rfl
  | succ j =>
    show (σ j).rename Nat.succ = (σ' j).rename Nat.succ
    rw [h j (Nat.lt_of_succ_lt_succ hi)]

theorem upSubN_congr {σ σ' : Nat → Term} {n : Nat} (h : ∀ i, i < n → σ i = σ' i) (k : Nat) :
    ∀ i, i < n + k → upSubN k σ i = upSubN k σ' i := by
  induction k with
  | zero => exact h
  | succ k ih => exact upSub_congr ih

mutual
  theorem Term.subst_congr {σ σ' : Nat → Term} {n : Nat} (h : ∀ i, i < n → σ i = σ' i) :
      ∀ t : Term, t.scoped n = true → t.subst σ = t.subst σ'
    | .var i, ht => by
      simp only [Term.scoped, decide_eq_true_eq] at ht
      exact h i ht
    | .con _, _ => rfl
    | .const _, _ => rfl
    | .app f a, ht => by
      simp only [Term.scoped, Term.subst, Bool.and_eq_true] at ht ⊢
      rw [Term.subst_congr h f ht.1, Term.subst_congr h a ht.2]
    | .abs b, ht => by
      simp only [Term.scoped, Term.subst] at ht ⊢
      rw [Term.subst_congr (upSub_congr h) b ht]
    | .cas s alts, ht => by
      simp only [Term.scoped, Term.subst, Bool.and_eq_true] at ht ⊢
      rw [Term.subst_congr h s ht.1, Alts.subst_congr h alts ht.2]

  theorem Alts.subst_congr {σ σ' : Nat → Term} {n : Nat} (h : ∀ i, i < n → σ i = σ' i) :
      ∀ a : Alts, a.scoped n = true → a.subst σ = a.subst σ'
    | .nil, _ => rfl
    | .alt c k b rest, ht => by
      simp only [Alts.scoped, Alts.subst, Bool.and_eq_true] at ht ⊢
      rw [Term.subst_congr (upSubN_congr h k) b ht.1, Alts.subst_congr h rest ht.2]
end

/-- Closed terms are unchanged by any substitution. -/
theorem Term.closed_subst {t : Term} (h : t.closed) (σ : Nat → Term) : t.subst σ = t := by
  have : t.subst σ = t.subst Term.var :=
    Term.subst_congr (n := 0) (fun i hi => absurd hi (Nat.not_lt_zero i)) t h
  rw [this, Term.subst_var]

/-- Closed terms are unchanged by renaming. -/
theorem Term.closed_rename {t : Term} (h : t.closed) (ρ : Nat → Nat) : t.rename ρ = t := by
  have h1 : t.rename ρ = t.subst (fun i => Term.var (ρ i)) := by
    have := Term.subst_rename (fun i => Term.var i) ρ t
    rw [Term.subst_var] at this
    exact this
  rw [h1]
  exact Term.closed_subst h _

/-! ## `beta`, `instAlt`, `mkApp`, `spine` and substitution -/

theorem Term.beta_subst (b a : Term) (σ : Nat → Term) :
    (Term.beta b a).subst σ = Term.beta (b.subst (upSub σ)) (a.subst σ) := by
  unfold Term.beta
  rw [Term.subst_subst, Term.subst_subst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ n =>
    show (Term.var n).subst σ = ((σ n).rename Nat.succ).subst _
    rw [Term.subst_rename]
    show σ n = (σ n).subst Term.var
    rw [Term.subst_var]

theorem upSubN_lt (σ : Nat → Term) (n : Nat) : ∀ i, i < n → upSubN n σ i = Term.var i := by
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ k ih =>
    intro i hi
    cases i with
    | zero => rfl
    | succ j =>
      show (upSubN k σ j).rename Nat.succ = Term.var (j + 1)
      rw [ih j (Nat.lt_of_succ_lt_succ hi)]
      rfl

theorem Term.rename_id (t : Term) : t.rename (fun j => j) = t := by
  have h := Term.subst_rename Term.var (fun j => j) t
  have e : (fun i => Term.var ((fun j => j) i)) = Term.var := rfl
  rw [e, Term.subst_var, Term.subst_var] at h
  exact h

theorem upSubN_ge (σ : Nat → Term) (n : Nat) :
    ∀ i, n ≤ i → upSubN n σ i = (σ (i - n)).rename (fun j => j + n) := by
  induction n with
  | zero =>
    intro i _
    exact (Term.rename_id (σ i)).symm
  | succ k ih =>
    intro i hi
    cases i with
    | zero => exact absurd hi (Nat.not_succ_le_zero k)
    | succ j =>
      show ((upSubN k σ j)).rename Nat.succ = (σ (j + 1 - (k + 1))).rename _
      rw [ih j (Nat.le_of_succ_le_succ hi), Term.rename_rename]
      have e : j + 1 - (k + 1) = j - k := by omega
      rw [e]
      have f : (Nat.succ ∘ fun j => j + k) = fun j => j + (k + 1) := by
        funext j; rfl
      rw [f]

end MM
