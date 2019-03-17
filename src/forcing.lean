import .bvm_extras .pSet_ordinal

open ordinal cardinal lattice bSet

noncomputable theory

local infix ` ⟹ `:65 := lattice.imp

local infix ` ⇔ `:50 := lattice.biimp

universe u

namespace bSet
section cardinal_preservation
variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

lemma AE_of_check_larger_than_check (x y : pSet.{u}) {f : bSet 𝔹} {Γ} {h_nonzero : ⊥ < Γ} (H : Γ ≤ (is_func f) ⊓ ⨅v, v ∈ᴮ y̌ ⟹ ⨆w, w ∈ᴮ x̌ ⊓ pair w v ∈ᴮ f) :
  ∀ i : y.type, ∃ j : x.type, ⊥ < (is_func f) ⊓ (pair ((x.func j)̌ ) ((y.func i)̌ )) ∈ᴮ f :=
begin
  intro i_v, bv_split_at H, replace H_1_1 := H_1_1 ((y.func i_v)̌ ), simp[check_mem'] at H_1_1,
  have H' : Γ ≤ is_func f ⊓ ⨆ (w : bSet 𝔹), w ∈ᴮ x̌  ⊓ pair w (pSet.func y i_v̌)  ∈ᴮ f,
    by bv_split_goal,
  rw[inf_supr_eq] at H',
  replace H' := le_trans H' (by {apply supr_le, intro i, recover, show 𝔹,
    from ⨆ (i : bSet 𝔹), i ∈ᴮ x̌ ⊓ (is_func f ⊓ pair i (pSet.func y i_v̌)  ∈ᴮ f),
    apply bv_use i, apply le_of_eq, ac_refl}),
  replace H' := lt_of_lt_of_le h_nonzero H',
  have := @bounded_exists 𝔹 _ (x̌) (λ z, is_func f ⊓ pair z ((y.func i_v)̌ ) ∈ᴮ f),
  rw[<-this] at H', swap,
    {intros x' y',
    /- `tidy_context` says -/ apply poset_yoneda, intros Γ_1 a,
    simp only [le_inf_iff] at a H ⊢, cases a, cases H, cases a_right, refine ⟨‹_›, _⟩,
    have : Γ_1 ≤ pair x' ((y.func i_v)̌ ) =ᴮ pair y' ((y.func i_v)̌ ),
     from subst_congr_pair_left' ‹_›, apply subst_congr_mem_left'; from ‹_›},
    {cases x, cases y, convert nonzero_wit H', ext,
      dsimp with cleanup, rw[top_inf_eq], refl}
end
end cardinal_preservation
end bSet

namespace pSet

@[reducible]noncomputable def ℵ₁ : pSet.{0} := ordinal.mk (aleph 1).ord

@[reducible]noncomputable def ℵ₂ : pSet.{0} := ordinal.mk (aleph 2).ord

@[simp, cleanup]lemma Union_type {x : pSet} : (type (Union x)) = Σ(a:x.type), (x.func a).type :=
by induction x; refl

@[simp, cleanup]lemma Union_type' {α : Type u} {A : α → pSet.{u}} :
  (Union (mk α A)).type = Σa, (A a).type := rfl

end pSet

open pSet

-- /-- A well-ordered type order-isomorphic to ℵ₂ -/
-- @[reducible]noncomputable def ℵ₂' : Well_order.{0} := (aleph 2).ord.out

-- /-- (ℕ, <) is, by definition, a well-ordered type order-isomorphic to ℵ₀ -/
-- def ℵ₀' : Well_order.{0} := ⟨ℕ, (<), by apply_instance⟩


def is_regular_open : set (set(ℵ₂.type × ℕ)) → Prop := sorry

def 𝔹 : Type := {S // is_regular_open S}
instance 𝔹_boolean_algebra : nontrivial_complete_boolean_algebra 𝔹 := sorry
/-- The principal regular open associated to a pair (ν, n) is the collection of all subsets of
    ℵ₂ × ℕ which contain (ν, n). -/
def principal_open (ν : (ℵ₂̌  : bSet 𝔹).type) (n : ℕ) : 𝔹 :=
begin
  simp at ν, use {S | (ν,n) ∈ S}, sorry
end

namespace cohen_real

/-- `cohen_real.χ ν` is the indicator function on ℕ induced by every ordinal less than ℵ₂ -/
def χ (ν : (ℵ₂̌  : bSet 𝔹).type) : ℕ → 𝔹 :=
  λ n, principal_open ν n

/-- `cohen_real.mk ν` is the subset of (ω : bSet 𝔹) induced by `cohen_real.χ ν` -/
def mk (ν : (ℵ₂̌  : bSet 𝔹).type) : bSet 𝔹 :=
  @set_of_indicator 𝔹 _ omega $ λ n, χ ν n.down

/-- bSet 𝔹 believes that each `mk ν` is a subset of omega -/
lemma definite {ν} {Γ} : Γ ≤ mk ν ⊆ᴮ omega :=
by simp[mk, subset_unfold]; from λ _, by {bv_imp_intro, from omega_definite}

/-- bSet 𝔹 believes that each `mk ν` is an element of 𝒫(ω) -/
lemma definite' {ν} {Γ} : Γ ≤ mk ν ∈ᴮ bv_powerset omega := bv_powerset_spec.mp definite

/-- Whenever ν₁ ≠ ν₂ < ℵ₂, bSet 𝔹 believes that `mk ν₁` and `mk ν₂` are distinct -/
lemma inj {ν₁ ν₂} (H_neq : ν₁ ≠ ν₂) : (mk ν₁) =ᴮ (mk ν₂) ≤ ⊥ :=
sorry -- this lemma requires us to view the Cohen poset as a dense subset of 𝔹
-- see Lemma 5.22 in flypitch-notes

end cohen_real

local notation `ℵ₀` := (omega : bSet 𝔹)
local notation `𝔠` := (bv_powerset ℵ₀ : bSet 𝔹)

lemma Card_ℵ₁ : ⊤ ≤ Card(ℵ₁̌  : bSet 𝔹) := sorry

lemma Card_ℵ₂ : ⊤ ≤ Card (ℵ₂̌  : bSet 𝔹) := sorry

lemma ℵ₀_lt_ℵ₁ : ⊤ ≤ ℵ₀ ∈ᴮ ℵ₁̌  := sorry

lemma ℵ₁_lt_ℵ₂ : ⊤ ≤ (ℵ₁̌ : bSet 𝔹) ∈ᴮ (ℵ₂̌ : bSet 𝔹) := sorry


noncomputable def neg_CH_func : bSet 𝔹 := @function.mk _ _ (ℵ₂̌ )
  (λ x, cohen_real.mk x)
begin
  sorry
end
theorem ℵ₂_le_𝔠 : ⊤ ≤ is_func' (ℵ₂̌ ) 𝔠 (neg_CH_func) ⊓ is_inj (neg_CH_func) :=
begin
apply le_inf,

  {unfold neg_CH_func, apply le_inf, apply le_inf, apply mk_is_func,
    simp only [subset_unfold] with cleanup,
    bv_intro ν, bv_imp_intro, 
    have : Γ ≤ (ℵ₂̌ ).func ν ∈ᴮ ℵ₂̌  ⊓ (cohen_real.mk ν ∈ᴮ bv_powerset ℵ₀),
      by {apply le_inf, from le_trans H (by apply mem.mk'),
          from cohen_real.definite'},
    from le_trans this (by apply prod_mem),

    bv_intro w₁, bv_imp_intro, rw[mem_unfold] at H,
    bv_cases_at H ν, apply bv_use (cohen_real.mk ν),
    rw[mem_unfold], apply bv_use ν, bv_split,
    from le_inf ‹_› (by apply le_trans H_1_right; apply subst_congr_pair_left)},

  {apply mk_inj_of_inj, from λ _ _ _, cohen_real.inj ‹_›},
end
