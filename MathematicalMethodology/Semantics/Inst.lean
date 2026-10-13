import MathematicalMethodology.Semantics.Scope

/-!
# Instantiation facts

`mkApp`, `spine`, `Alts.find?` and `instAlt` versus substitution and scoping.
-/

namespace MM

/-! ## `mkApp` and `spine` -/

theorem Term.mkApp_nil (h : Term) : Term.mkApp h [] = h := rfl

theorem Term.mkApp_cons (h a : Term) (as : List Term) :
    Term.mkApp h (a :: as) = Term.mkApp (Term.app h a) as := rfl

theorem Term.mkApp_append_single (h : Term) (as : List Term) (a : Term) :
    Term.mkApp h (as ++ [a]) = Term.app (Term.mkApp h as) a := by
  simp [Term.mkApp, List.foldl_append]

theorem Term.mkApp_subst (h : Term) (args : List Term) (σ : Nat → Term) :
    (Term.mkApp h args).subst σ = Term.mkApp (h.subst σ) (args.map (·.subst σ)) := by
  induction args generalizing h with
  | nil => rfl
  | cons a as ih =>
    rw [Term.mkApp_cons, ih]
    rfl

theorem Term.mkApp_scoped {n : Nat} (h : Term) (args : List Term) (hh : h.scoped n = true)
    (ha : ∀ a ∈ args, a.scoped n = true) : (Term.mkApp h args).scoped n = true := by
  induction args generalizing h with
  | nil => exact hh
  | cons a as ih =>
    rw [Term.mkApp_cons]
    apply ih
    · simp only [Term.scoped, Bool.and_eq_true]
      exact ⟨hh, ha a (List.mem_cons_self ..)⟩
    · intro b hb; exact ha b (List.mem_cons_of_mem _ hb)

theorem Term.spine_eq : ∀ t : Term, t = Term.mkApp t.spine.1 t.spine.2
  | .var _ => rfl
  | .con _ => rfl
  | .const _ => rfl
  | .abs _ => rfl
  | .cas _ _ => rfl
  | .app f a => by
    have ih := Term.spine_eq f
    show Term.app f a = Term.mkApp f.spine.1 (f.spine.2 ++ [a])
    rw [Term.mkApp_append_single, ← ih]

theorem Term.eq_mkApp_of_spine {t h : Term} {args : List Term} (e : t.spine = (h, args)) :
    t = Term.mkApp h args := by
  have := Term.spine_eq t
  rw [e] at this
  exact this

/-! ## `Alts.find?` -/

theorem Alts.find?_subst (σ : Nat → Term) (c : String) :
    ∀ (a : Alts) (n : Nat) (body : Term), a.find? c = some (n, body) →
      (a.subst σ).find? c = some (n, body.subst (upSubN n σ))
  | .nil, _, _, h => by simp [Alts.find?] at h
  | .alt d k b rest, n, body, h => by
    simp only [Alts.find?, Alts.subst] at h ⊢
    by_cases hc : c = d
    · rw [if_pos hc] at h
      rw [if_pos hc]
      have e := Option.some.inj h
      have h1 : k = n := congrArg Prod.fst e
      have h2 : b = body := congrArg Prod.snd e
      subst h1; subst h2; rfl
    · rw [if_neg hc] at h
      rw [if_neg hc]
      exact Alts.find?_subst σ c rest n body h

/-! ## `instAlt` -/

theorem getD_map_lt {α β : Type} (f : α → β) (d : α) (d' : β) :
    ∀ (l : List α) (k : Nat), k < l.length → (l.map f).getD k d' = f (l.getD k d)
  | [], k, h => absurd h (Nat.not_lt_zero k)
  | _ :: _, 0, _ => rfl
  | _ :: as, k + 1, h => getD_map_lt f d d' as k (Nat.lt_of_succ_lt_succ h)

theorem Term.instAlt_subst (n : Nat) (args : List Term) (body : Term) (σ : Nat → Term)
    (hlen : args.length = n) :
    (Term.instAlt n args body).subst σ =
      Term.instAlt n (args.map (·.subst σ)) (body.subst (upSubN n σ)) := by
  unfold Term.instAlt
  rw [Term.subst_subst, Term.subst_subst]
  congr 1
  funext i
  by_cases hi : i < n
  · simp only [if_pos hi]
    rw [upSubN_lt σ n i hi]
    show _ = (if i < n then _ else _)
    rw [if_pos hi]
    exact (getD_map_lt (·.subst σ) (Term.var 0) (Term.var 0) args (n - 1 - i)
      (by omega)).symm
  · simp only [if_neg hi]
    rw [upSubN_ge σ n i (by omega), Term.subst_rename]
    show σ (i - n) = _
    have : (fun j => (if j + n < n then
        (List.map (·.subst σ) args).getD (n - 1 - (j + n)) (Term.var 0)
        else Term.var (j + n - n))) = Term.var := by
      funext j
      rw [if_neg (by omega)]
      congr 1
      omega
    rw [this, Term.subst_var]

end MM
