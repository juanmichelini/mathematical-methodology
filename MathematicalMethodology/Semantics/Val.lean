import MathematicalMethodology.Semantics.Conv
import MathematicalMethodology.Tactical.Cert

/-!
# Values, denotation and typing

The semantic notions the soundness theorem is stated with.

* `IsVal data ty v`: `v` is a closed *value* of type `ty`: a constructor applied to
  values of the declared field types.  A type with no declaration is *opaque*: every
  closed term is a value of it.
* `Denotes env data ty t`: `t` is closed and convertible to a value of type `ty`.
* `DenotesF tys r t`: `t` denotes a function from arguments of types `tys` to `r`.
* `SigSound cx`: the declared signatures of the defined functions are right (the
  functions are total on values).  This is an *assumption* of the soundness theorem.
* `DataWF data`: data type names are unique.  Also an assumption.

`typeOf_sound` says that a term the checker types, with values substituted for its
variables, denotes a value of its type.
-/

namespace MM

/-! ## Values -/

theorem getD_of_lt {α : Type} (l : List α) (j : Nat) (hj : j < l.length) (d : α) :
    l.getD j d = l[j] := by
  simp [List.getD_eq_getElem?_getD, hj]

inductive IsVal (data : List DataDecl) : String → Term → Prop
  | opq (ty : String) (v : Term) :
      data.find? (·.name = ty) = none → v.closed → IsVal data ty v
  | ctor (ty : String) (d : DataDecl) (c : String) (fields : List String) (args : List Term) :
      data.find? (·.name = ty) = some d → (c, fields) ∈ d.ctors →
      args.length = fields.length →
      (∀ j, j < fields.length → IsVal data (fields.getD j "") (args.getD j (.var 0))) →
      IsVal data ty (Term.mkApp (.con c) args)

theorem IsVal.closed {data : List DataDecl} {ty : String} {v : Term} (h : IsVal data ty v) :
    v.closed := by
  induction h with
  | opq ty v _ hc => exact hc
  | ctor ty d c fields args _ _ hlen _ ih =>
    apply Term.mkApp_scoped
    · rfl
    · intro a ha
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      have := ih j (by omega)
      rw [getD_of_lt args j hj] at this
      exact this

def Denotes (env : Env) (data : List DataDecl) (ty : String) (t : Term) : Prop :=
  t.closed ∧ ∃ u, IsVal data ty u ∧ Conv env t u

def DenotesF (env : Env) (data : List DataDecl) : List String → String → Term → Prop
  | [], r, t => Denotes env data r t
  | a :: ts, r, t => t.closed ∧ ∀ x, Denotes env data a x → DenotesF env data ts r (.app t x)

/-- A substitution that sends the variables of `ctx` to values of the right types. -/
def ValSub (data : List DataDecl) (ctx : List String) (σ : Nat → Term) : Prop :=
  ∀ i ty, ctx[i]? = some ty → IsVal data ty (σ i)

/-- Assumption: the declared signatures of defined functions are right. -/
def SigSound (cx : Ctx) : Prop :=
  ∀ f tys res, cx.funSig f = some (tys, res) → DenotesF cx.env cx.data tys res (.const f)

/-- Assumption: data type names are unique. -/
def DataWF (data : List DataDecl) : Prop :=
  ∀ d ∈ data, data.find? (·.name = d.name) = some d

/-! ## Lists of denoting terms -/

inductive DenL (env : Env) (data : List DataDecl) : List String → List Term → Prop
  | nil : DenL env data [] []
  | cons {t : String} {x : Term} {ts : List String} {xs : List Term} :
      Denotes env data t x → DenL env data ts xs → DenL env data (t :: ts) (x :: xs)

theorem DenL.length {env : Env} {data : List DataDecl} {tys : List String} {xs : List Term}
    (h : DenL env data tys xs) : xs.length = tys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem DenL.closed {env : Env} {data : List DataDecl} {tys : List String} {xs : List Term}
    (h : DenL env data tys xs) : ∀ a ∈ xs, a.closed := by
  induction h with
  | nil => intro a ha; simp at ha
  | cons hx _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hx.1
    · exact ih a ha

theorem DenL.append_single {env : Env} {data : List DataDecl} {tys : List String}
    {xs : List Term} (h : DenL env data tys xs) {t : String} {x : Term}
    (hx : Denotes env data t x) : DenL env data (tys ++ [t]) (xs ++ [x]) := by
  induction h with
  | nil => exact .cons hx .nil
  | cons h1 _ ih => exact .cons h1 ih

theorem mkApp_conv_head {env : Env} {a b : Term} (h : Conv env a b) :
    ∀ xs : List Term, Conv env (Term.mkApp a xs) (Term.mkApp b xs)
  | [] => h
  | x :: xs => mkApp_conv_head (Conv.app h (.refl x)) xs

theorem DenL.toVals {env : Env} {data : List DataDecl} {tys : List String} {xs : List Term}
    (hd : DenL env data tys xs) :
    ∃ vs : List Term, vs.length = xs.length ∧
      (∀ j, j < tys.length → IsVal data (tys.getD j "") (vs.getD j (.var 0))) ∧
      ∀ h, Conv env (Term.mkApp h xs) (Term.mkApp h vs) := by
  induction hd with
  | nil => exact ⟨[], rfl, fun j hj => absurd hj (Nat.not_lt_zero _), fun h => .refl _⟩
  | @cons t x ts xs hx _ ih =>
    obtain ⟨_, u, hu, hxu⟩ := hx
    obtain ⟨vs, hl, hv, hc⟩ := ih
    refine ⟨u :: vs, by simp [hl], ?_, ?_⟩
    · intro j hj
      cases j with
      | zero => exact hu
      | succ j => exact hv j (Nat.lt_of_succ_lt_succ hj)
    · intro h
      exact .trans (hc (.app h x)) (mkApp_conv_head (Conv.app (.refl h) hxu) vs)

/-! ## Constructors denote -/

theorem con_denotes {env : Env} {data : List DataDecl} (c : String) (dname : String)
    (d : DataDecl) (hd : data.find? (·.name = dname) = some d) :
    ∀ (rest pre : List String) (xs : List Term), DenL env data pre xs →
      (c, pre ++ rest) ∈ d.ctors →
      DenotesF env data rest dname (Term.mkApp (.con c) xs)
  | [], pre, xs, hx, hm => by
    obtain ⟨vs, hl, hv, hc⟩ := hx.toVals
    have hlen := hx.length
    refine ⟨Term.mkApp_scoped _ _ rfl hx.closed, Term.mkApp (.con c) vs, ?_, hc _⟩
    refine IsVal.ctor dname d c pre vs hd (by simpa using hm) (by omega) ?_
    exact hv
  | a :: rest, pre, xs, hx, hm => by
    refine ⟨Term.mkApp_scoped _ _ rfl hx.closed, ?_⟩
    intro x hxd
    have h1 := hx.append_single hxd
    have h2 := con_denotes c dname d hd rest (pre ++ [a]) (xs ++ [x]) h1
      (by simpa using hm)
    rw [Term.mkApp_append_single] at h2
    exact h2

/-! ## The checker's typing is sound -/

theorem Ctx.ctorSig_spec {cx : Ctx} {c : String} {fields : List String} {dname : String}
    (h : cx.ctorSig c = some (fields, dname)) :
    ∃ d, d ∈ cx.data ∧ (c, fields) ∈ d.ctors ∧ d.name = dname := by
  unfold Ctx.ctorSig at h
  rw [List.findSome?_eq_some_iff] at h
  obtain ⟨l₁, d, l₂, hl, hf, _⟩ := h
  refine ⟨d, by rw [hl]; simp, ?_, ?_⟩
  · cases hfind : d.ctors.find? (·.1 = c) with
    | none => simp [hfind] at hf
    | some p =>
      simp only [hfind, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      have hp := List.mem_of_find?_eq_some hfind
      have hc : p.1 = c := by simpa using List.find?_some hfind
      have : p = (c, fields) := by
        rw [← hc, ← hf.1]
      rw [← this]
      exact hp
  · cases hfind : d.ctors.find? (·.1 = c) with
    | none => simp [hfind] at hf
    | some p =>
      simp only [hfind, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      exact hf.2

theorem typeOf_sound {cx : Ctx} (hS : SigSound cx) (hD : DataWF cx.data) {ctx : List String}
    {σ : Nat → Term} (hσ : ValSub cx.data ctx σ) :
    ∀ (t : Term) (ts : List String) (r : String), cx.typeOf ctx t = some (ts, r) →
      DenotesF cx.env cx.data ts r (t.subst σ)
  | .var i, ts, r, h => by
    simp only [Ctx.typeOf] at h
    cases hc : ctx[i]? with
    | none => simp [hc] at h
    | some ty =>
      simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hv := hσ i ty hc
      exact ⟨hv.closed, σ i, hv, .refl _⟩
  | .con c, ts, r, h => by
    simp only [Ctx.typeOf] at h
    obtain ⟨d, hd, hm, rfl⟩ := Ctx.ctorSig_spec h
    exact con_denotes c d.name d (hD d hd) ts [] [] .nil (by simpa using hm)
  | .const f, ts, r, h => hS f ts r h
  | .abs _, _, _, h => by simp [Ctx.typeOf] at h
  | .cas _ _, _, _, h => by simp [Ctx.typeOf] at h
  | .app f a, ts, r, h => by
    simp only [Ctx.typeOf] at h
    split at h
    · rename_i t' ts' r' u hf ha
      split at h
      · rename_i hu
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h1 := typeOf_sound hS hD hσ f _ _ hf
        have h2 := typeOf_sound hS hD hσ a _ _ ha
        subst hu
        exact h1.2 _ h2
      · simp at h
    · simp at h

end MM
