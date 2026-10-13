import MathematicalMethodology.Examples.Lists
import MathematicalMethodology.Semantics.CheckSound

/-!
# The list example satisfies the soundness assumptions

`Cert.check_sound` is conditional on `EnvClosed`, `SigSound` and `DataWF`.  Here they
are proved for `listCtx`, so the accepted development (`append_nil`, `append_assoc`,
`rev_append`, `rev_rev`) is *proved sound*: each lemma holds, as a `Conv` equation, for
all value instances of its variables.

The proofs of `SigSound` are by induction on the value of the first argument,
using the computation facts below.  Those facts are first checked symbolically (by
evaluating on variables, with `computeSafe_sound`) and then instantiated with
`Conv.subst`, so no reasoning about renaming is needed.
-/

namespace MM.Examples

open MM

/-! ## Assumptions -/

theorem listEnvClosed : EnvClosed listCtx.env := by
  intro f t h
  simp only [listCtx, Env.lookup] at h
  by_cases h1 : f = "append"
  · subst h1
    simp at h
    subst h
    exact (rfl : appendDef.scoped 0 = true)
  · by_cases h2 : f = "rev"
    · subst h2
      simp at h
      subst h
      exact (rfl : revDef.scoped 0 = true)
    · have h1' : ¬ "append" = f := fun e => h1 e.symm
      have h2' : ¬ "rev" = f := fun e => h2 e.symm
      simp [h1', h2'] at h

theorem listDataWF : DataWF listCtx.data := by
  intro d hd
  simp only [listCtx, List.mem_singleton] at hd
  subst hd
  rfl

/-! ## Computation facts, as `Conv` -/

/-- Variables `0, 1, 2` replaced by `a, b, c`. -/
def σ3 (a b c : Term) : Nat → Term
  | 0 => a
  | 1 => b
  | 2 => c
  | k + 3 => .var k

theorem append_nil_conv (y : Term) : Conv listCtx.env (appendT nilT y) y :=
  Conv.subst listEnvClosed
    (Term.computeSafe_sound listCtx.env 200 (appendT nilT (.var 0)) (.var 0) (by decide))
    (σ3 y y y)

theorem append_cons_conv (h t y : Term) :
    Conv listCtx.env (appendT (consT h t) y) (consT h (appendT t y)) :=
  Conv.subst listEnvClosed
    (Term.computeSafe_sound listCtx.env 200 (appendT (consT (.var 0) (.var 1)) (.var 2))
      (consT (.var 0) (appendT (.var 1) (.var 2))) (by decide))
    (σ3 h t y)

theorem rev_nil_conv : Conv listCtx.env (revT nilT) nilT :=
  Term.computeSafe_sound listCtx.env 200 (revT nilT) nilT (by decide)

theorem rev_cons_conv (h t : Term) :
    Conv listCtx.env (revT (consT h t)) (appendT (revT t) (consT h nilT)) :=
  Conv.subst listEnvClosed
    (Term.computeSafe_sound listCtx.env 200 (revT (consT (.var 0) (.var 1)))
      (appendT (revT (.var 1)) (consT (.var 0) nilT)) (by decide))
    (σ3 h t t)

/-! ## Constructors denote -/

theorem list_find : listCtx.data.find? (·.name = "List") =
    some { name := "List", ctors := [("nil", []), ("cons", ["Elem", "List"])] } := rfl

theorem nil_denotes : Denotes listCtx.env listCtx.data "List" nilT :=
  con_denotes (env := listCtx.env) "nil" "List" _ list_find [] [] [] .nil (by simp)

theorem cons_denotes {h t : Term} (hh : Denotes listCtx.env listCtx.data "Elem" h)
    (ht : Denotes listCtx.env listCtx.data "List" t) :
    Denotes listCtx.env listCtx.data "List" (consT h t) :=
  (con_denotes (env := listCtx.env) "cons" "List" _ list_find ["Elem", "List"] [] [] .nil
    (by simp)).2 h hh |>.2 t ht

theorem isVal_elem {h : Term} (hc : h.closed) : IsVal listCtx.data "Elem" h :=
  IsVal.opq "Elem" h rfl hc

/-! ## `append` and `rev` map values to values -/

theorem append_den : ∀ (ty : String) (u : Term), IsVal listCtx.data ty u → ty = "List" →
    ∀ x y, x.closed → Conv listCtx.env x u →
      Denotes listCtx.env listCtx.data "List" y →
      Denotes listCtx.env listCtx.data "List" (appendT x y) := by
  intro ty u hu
  induction hu with
  | opq ty w hnone _ =>
    intro hty
    subst hty
    rw [list_find] at hnone; cases hnone
  | ctor ty d c fields args hfd hmem hlen hargs ih =>
    intro hty x y hx hxu hy
    subst hty
    simp only [listCtx, List.find?_cons, List.find?_nil] at hfd
    have hd : d = { name := "List", ctors := [("nil", []), ("cons", ["Elem", "List"])] } := by
      simpa using hfd.symm
    subst hd
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have : args = [] := List.length_eq_zero_iff.mp hlen
      subst this
      have h1 : Conv listCtx.env (appendT x y) (appendT nilT y) :=
        .app (.app (.refl _) hxu) (.refl _)
      exact Denotes.of_conv hy (h1.trans (append_nil_conv y))
        (Term.closed_app (Term.closed_app rfl hx) hy.1)
    · obtain ⟨h, t, rfl⟩ : ∃ h t, args = [h, t] := by
        rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
        · simp at hlen
        · simp at hlen
        · exact ⟨a, b, rfl⟩
        · simp at hlen
      have hhc := (hargs 0 (by simp)).closed
      have htc := (hargs 1 (by simp)).closed
      have ih1 := ih 1 (by simp) rfl t y htc (.refl _) hy
      have h1 : Conv listCtx.env (appendT x y) (appendT (consT h t) y) :=
        .app (.app (.refl _) hxu) (.refl _)
      have hh : Denotes listCtx.env listCtx.data "Elem" h :=
        ⟨hhc, h, isVal_elem hhc, .refl _⟩
      exact Denotes.of_conv (cons_denotes hh ih1) (h1.trans (append_cons_conv h t y))
        (Term.closed_app (Term.closed_app rfl hx) hy.1)

theorem append_den' {x y : Term} (hx : Denotes listCtx.env listCtx.data "List" x)
    (hy : Denotes listCtx.env listCtx.data "List" y) :
    Denotes listCtx.env listCtx.data "List" (appendT x y) := by
  obtain ⟨hxc, u, hu, hxu⟩ := hx
  exact append_den "List" u hu rfl x y hxc hxu hy

theorem rev_den : ∀ (ty : String) (u : Term), IsVal listCtx.data ty u → ty = "List" →
    ∀ x, x.closed → Conv listCtx.env x u →
      Denotes listCtx.env listCtx.data "List" (revT x) := by
  intro ty u hu
  induction hu with
  | opq ty w hnone _ =>
    intro hty
    subst hty
    rw [list_find] at hnone; cases hnone
  | ctor ty d c fields args hfd hmem hlen hargs ih =>
    intro hty x hx hxu
    subst hty
    simp only [listCtx, List.find?_cons, List.find?_nil] at hfd
    have hd : d = { name := "List", ctors := [("nil", []), ("cons", ["Elem", "List"])] } := by
      simpa using hfd.symm
    subst hd
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have : args = [] := List.length_eq_zero_iff.mp hlen
      subst this
      have h1 : Conv listCtx.env (revT x) (revT nilT) := .app (.refl _) hxu
      exact Denotes.of_conv nil_denotes (h1.trans rev_nil_conv) (Term.closed_app rfl hx)
    · obtain ⟨h, t, rfl⟩ : ∃ h t, args = [h, t] := by
        rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
        · simp at hlen
        · simp at hlen
        · exact ⟨a, b, rfl⟩
        · simp at hlen
      have hhc := (hargs 0 (by simp)).closed
      have htc := (hargs 1 (by simp)).closed
      have ih1 := ih 1 (by simp) rfl t htc (.refl _)
      have h1 : Conv listCtx.env (revT x) (revT (consT h t)) := .app (.refl _) hxu
      have hh : Denotes listCtx.env listCtx.data "Elem" h :=
        ⟨hhc, h, isVal_elem hhc, .refl _⟩
      exact Denotes.of_conv (append_den' ih1 (cons_denotes hh nil_denotes))
        (h1.trans (rev_cons_conv h t)) (Term.closed_app rfl hx)

theorem listSigSound : SigSound listCtx := by
  intro f tys res h
  simp only [Ctx.funSig, listCtx] at h
  by_cases h1 : f = "append"
  · subst h1
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, fun x hx => ⟨Term.closed_app rfl hx.1, fun y hy => ?_⟩⟩
    obtain ⟨hxc, u, hu, hxu⟩ := hx
    exact append_den "List" u hu rfl x y hxc hxu hy
  · by_cases h2 : f = "rev"
    · subst h2
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, fun x hx => ?_⟩
      obtain ⟨hxc, u, hu, hxu⟩ := hx
      exact rev_den "List" u hu rfl x hxc hxu
    · have h1' : ¬ "append" = f := fun e => h1 e.symm
      have h2' : ¬ "rev" = f := fun e => h2 e.symm
      simp [h1', h2'] at h

/-! ## The development is proved sound -/

theorem development_accepted : (checkDevelopment listCtx development []).toBool = true := by
  decide

/-- Every lemma of the list development holds, as a `Conv` equation, for all value
instances of its variables.  In particular `rev (rev xs) = xs`. -/
theorem development_valid : ∀ e ∈ development, LemmaValid listCtx e.2.1.toRule := by
  cases hc : checkDevelopment listCtx development [] with
  | error e =>
    have hacc := development_accepted
    rw [hc] at hacc
    simp [Except.toBool] at hacc
  | ok rules =>
    exact checkDevelopment_valid listEnvClosed listSigSound listDataWF development rules hc

theorem revRev_valid : LemmaValid listCtx revRev.toRule :=
  development_valid ("rev_rev", revRev, revRevCert) (by simp [development])

end MM.Examples
