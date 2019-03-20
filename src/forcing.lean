import .bvm_extras .pSet_ordinal .set_theory cohen_poset

open ordinal cardinal lattice bSet

noncomputable theory

local attribute [instance, priority 0] classical.prop_decidable

local attribute [simp] omega_le_aleph

local infix ` ⟹ `:65 := lattice.imp

local infix ` ⇔ `:50 := lattice.biimp

local prefix `#`:70 := cardinal.mk

universe u

def CCC (𝔹 : Type u) [boolean_algebra 𝔹] : Prop :=
  ∀ ι : Type u, ∀ 𝓐 : ι → 𝔹, (∀ i, ⊥ < 𝓐 i) →
    (∀ i j, i ≠ j → 𝓐 i ⊓ 𝓐 j ≤ ⊥) → #ι = cardinal.omega

namespace bSet
section cardinal_preservation
local notation `ω` := cardinal.omega


variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

lemma AE_of_check_larger_than_check (x y : pSet.{u}) {f : bSet 𝔹} {Γ}
  (H : Γ ≤ (is_func f) ⊓ ⨅v, v ∈ᴮ y̌ ⟹ ⨆w, w ∈ᴮ x̌ ⊓ pair w v ∈ᴮ f) (h_nonzero : ⊥ < Γ) :
  ∀ i : y.type, ∃ j : x.type, ⊥ < (is_func f) ⊓ (pair ((x.func j)̌ ) ((y.func i)̌ )) ∈ᴮ f :=
begin
  intro i_v, bv_split_at H, replace H_1_1 := H_1_1 ((y.func i_v)̌ ), simp[check_mem'] at H_1_1,
  have H' : Γ ≤ is_func f ⊓ ⨆ (w : bSet 𝔹), w ∈ᴮ x̌  ⊓ pair w (pSet.func y i_v̌)  ∈ᴮ f,
    from context_and_intro ‹_› ‹_›,
  rw[inf_supr_eq] at H',
  replace H' := le_trans H' (by {apply supr_le, intro i, recover, show 𝔹,
    from ⨆ (i : bSet 𝔹), i ∈ᴮ x̌ ⊓ (is_func f ⊓ pair i (pSet.func y i_v̌)  ∈ᴮ f),
    apply bv_use i, apply le_of_eq, ac_refl}),
  replace H' := lt_of_lt_of_le h_nonzero H',
  have := @bounded_exists 𝔹 _ (x̌) (λ z, is_func f ⊓ pair z ((y.func i_v)̌ ) ∈ᴮ f),
  rw[<-this] at H', swap,
    {intros x' y',
    apply poset_yoneda, intros Γ_1 a,
    simp only [le_inf_iff] at a H ⊢, cases a, cases H, cases a_right, refine ⟨‹_›, _⟩,
    have : Γ_1 ≤ pair x' ((y.func i_v)̌ ) =ᴮ pair y' ((y.func i_v)̌ ),
     from subst_congr_pair_left' ‹_›, apply subst_congr_mem_left'; from ‹_›},
    {cases x, cases y, convert nonzero_wit H', ext1,
      dsimp with cleanup, rw[top_inf_eq]}
end

variables
  (η₁ η₂ : pSet.{u}) (H_infinite : ω ≤ #(η₁.type))
  (H_lt : #(η₁.type) < #(η₂.type))
  (H_inj₂ : ∀ x y, x ≠ y → ¬ pSet.equiv (η₂.func x) (η₂.func y))
  (f : bSet 𝔹) (g : η₂.type → η₁.type)
  (H : ∀ β : η₂.type, (⊥ : 𝔹) < is_func f ⊓ pair ((η₁.func (g β)̌ ) ) ((η₂.func β)̌ )∈ᴮ f)

include H_infinite H_lt H_inj₂ f H
lemma not_CCC_of_uncountable_fiber (H_ex : ∃ ξ : η₁.type, ω < #(g⁻¹' {ξ})) : ¬ CCC 𝔹 :=
begin
  cases H_ex with ξ H_ξ,
  let 𝓐 : (g⁻¹'{ξ}) → 𝔹 :=
    λ β, is_func f ⊓ (pair ((η₁.func (g β.val))̌ ) ((η₂.func β.val)̌ )) ∈ᴮ f,
  have 𝓐_nontriv : ∀ β, ⊥ < 𝓐 β,
    from λ _, by apply H,
  have 𝓐_anti : ∀ β₁ β₂, β₁ ≠ β₂ → (𝓐 β₁) ⊓ (𝓐 β₂) ≤ ⊥,
    by {intros β₁ β₂ h_sep, dsimp[𝓐],
    /- `tidy_context` says -/ apply poset_yoneda, intros Γ a,
    cases β₂, cases β₁, cases H_ξ, cases H_lt, cases β₁_property, cases β₂_property,
    work_on_goal 0 { induction β₂_property, simp only [le_inf_iff] at a,
                     cases a, cases a_right, cases a_left },
    work_on_goal 1 { induction β₁_property, simp only [le_inf_iff] at a,
                     cases a, cases a_right, cases a_left, solve_by_elim },
    work_on_goal 1 { cases β₂_property,
      work_on_goal 0 { induction β₂_property, simp only [le_inf_iff] at a,
        cases a, cases a_right, cases a_left, solve_by_elim}, simp only [le_inf_iff] at a,
        cases a, cases a_right, cases a_left, solve_by_elim},
    
    rw[β₁_property] at a_left_right,
    have H_le_eq : Γ ≤ ((η₂.func β₁_val)̌ ) =ᴮ ((η₂.func β₂_val)̌ ),
     by {apply funext; from ‹_›},
    from le_trans H_le_eq
           (by {rw[le_bot_iff], apply check_bv_eq_bot_of_not_equiv, apply H_inj₂, tidy})},
   intro H_CCC, specialize H_CCC (g⁻¹'{ξ}) ‹_› ‹_› ‹_›,
   replace H_ξ := (lt_iff_le_and_ne.mp H_ξ).right.symm, contradiction
end

end cardinal_preservation
end bSet

open bSet

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

theorem 𝔹_CCC : CCC 𝔹 := sorry 
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

section neg_CH

local notation `ℵ₀` := (omega : bSet 𝔹)
local notation `𝔠` := (bv_powerset ℵ₀ : bSet 𝔹)
local infix `≺`:70 := (λ x y, -(larger_than x y))

lemma ℵ₀_lt_ℵ₁ : (⊤ : 𝔹)  ≤ ℵ₀ ≺ ℵ₁̌  :=
begin
  simp[larger_than, -top_le_iff], rw[<-imp_bot],
  bv_imp_intro, bv_cases_at H f, by_contra,
  have := classical.axiom_of_choice
            (AE_of_check_larger_than_check _ _ H_1 (bot_lt_iff_not_le_bot.mpr ‹_›)),
  cases this with g g_spec,
  suffices : ¬ CCC 𝔹, from (not_and_self _).mp ⟨this, 𝔹_CCC⟩,
  apply not_CCC_of_uncountable_fiber; try{assumption},
    {from le_of_eq (by simp)},
    {simp},
    {intros i₁ i₂ H_neq, from ordinal.mk_inj _ _ _ ‹_›},
    {dsimp at g, have := is_regular_aleph_one.right,
     have := infinite_pigeonhole g _ _,
     cases this with ξ H_ξ₁, use ξ, rw[H_ξ₁],
     all_goals{simp*}, rw[this], simp}
end

lemma ℵ₁_lt_ℵ₂ : (⊤ : 𝔹) ≤ ℵ₁̌  ≺ ℵ₂̌  :=
begin
  simp[larger_than, -top_le_iff], rw[<-imp_bot],
  bv_imp_intro, bv_cases_at H f, by_contra,
  have := classical.axiom_of_choice
            (AE_of_check_larger_than_check _ _ H_1 (bot_lt_iff_not_le_bot.mpr ‹_›)),
  cases this with g g_spec,
  suffices : ¬ CCC 𝔹, from (not_and_self _).mp ⟨this, 𝔹_CCC⟩,
  apply not_CCC_of_uncountable_fiber; try{assumption},
    {simp},
    {simp},
    {intros i₁ i₂ H_neq, from ordinal.mk_inj _ _ _ ‹_›},
    {dsimp at g, have := is_regular_aleph_two.right,
     have := infinite_pigeonhole g _ _,
     cases this with ξ H_ξ₁, use ξ, rw[H_ξ₁],
     all_goals{simp*}, rw[this], simp}
end

lemma cohen_real.mk_ext : ∀ (i j : type (ℵ₂̌  : bSet 𝔹)), func (ℵ₂̌ ) i =ᴮ func (ℵ₂̌ ) j ≤
  (λ (x : type (ℵ₂̌ )), cohen_real.mk x) i =ᴮ (λ (x : type (ℵ₂̌ )), cohen_real.mk x) j :=
begin
  intros i j, by_cases i = j,
   {simp[h]},
   {apply poset_yoneda, intros Γ a, simp only [le_inf_iff] at *,
     have : func (ℵ₂̌ ) i = (ℵ₂.func (check_cast i))̌ ,
       by simp[check_func],
     rw[this] at a,
     have : func (ℵ₂̌ ) j = (ℵ₂.func (check_cast j))̌ ,
       by simp[check_func],
     rw[this] at a,
   suffices : func ℵ₂ (check_cast i)̌  =ᴮ func ℵ₂ (check_cast j)̌  ≤ ⊥,
     from le_trans a (le_trans this bot_le),
   rw[le_bot_iff], apply check_bv_eq_bot_of_not_equiv,
   apply ordinal.mk_inj, unfold check_cast, intro H, cc}
end

noncomputable def neg_CH_func : bSet 𝔹 := @function.mk _ _ (ℵ₂̌ )
  (λ x, cohen_real.mk x) cohen_real.mk_ext

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

end neg_CH
