/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
import .bvm_extras .cantor_space

open ordinal cardinal lattice bSet

noncomputable theory

local attribute [instance] classical.prop_decidable

local attribute [simp] omega_le_aleph

local infix ` ⟹ `:65 := lattice.imp

local infix ` ⇔ `:50 := lattice.biimp

local prefix `#`:70 := cardinal.mk

local infix `≺`:70 := (λ x y, -(larger_than x y))

local infix `≼`:70 := (λ x y, injects_into x y)

universe u

namespace bSet
section cardinal_preservation
local notation `ω` := cardinal.omega
variables {𝔹 : Type u} [I : nontrivial_complete_boolean_algebra 𝔹]

include I

lemma AE_of_check_larger_than_check {x y : pSet.{u}} {Γ : 𝔹} (H_nonzero : ⊥ < Γ)
  (H : Γ ≤ larger_than x̌ y̌) (H_mem : ∃ z, z ∈ y) : ∃ f : bSet 𝔹, ∀ i : y.type, ∃ j : x.type, ⊥ < (is_func f) ⊓ (pair (x.func j)̌  (y.func i)̌  ∈ᴮ f) :=
begin
  replace H := surjects_onto_of_larger_than_and_exists_mem H (check_exists_mem ‹_›),
  unfold surjects_onto at H, have := maximum_principle (λ w, is_func' x̌ y̌ w ⊓ is_surj x̌ (y̌ : bSet 𝔹) w) _,
  cases this with f Hf, rw Hf at H, swap, {simp},
  use f, intro i_v, bv_split_at H,
  replace H_right := H_right (y.func i_v)̌ , simp [check_mem'] at H_right,
  replace H_right := exists_convert H_right _, cases H_right with w Hw, bv_split_at Hw,
  rcases eq_check_of_mem_check ‹_› Hw_left with ⟨j,Γ',HΓ'₁,HΓ'₂,H_eq⟩,
  use j, refine lt_of_lt_of_le HΓ'₁ (le_inf _ _),
    { exact le_trans HΓ'₂ (is_func_of_is_func' ‹_›) },
    { apply @bv_rw' _ _ _ _ _ (bv_symm H_eq) (λ z, pair z (y.func i_v)̌  ∈ᴮ f), exact B_ext_pair_mem_left,
      from le_trans ‹_› ‹_› },
  exact B_ext_inf (by simp) B_ext_pair_mem_left
end

variables
  (η₁ η₂ : pSet.{u}) (H_infinite : ω ≤ #(η₁.type))
  (H_lt : #(η₁.type) < #(η₂.type))
  (H_inj₂ : ∀ x y, x ≠ y → ¬ pSet.equiv (η₂.func x) (η₂.func y))
  (f : bSet 𝔹) (g : η₂.type → η₁.type)
  (H : ∀ β : η₂.type, (⊥ : 𝔹) < is_func f ⊓ pair (η₁.func (g β))̌  ((η₂.func β)̌ )∈ᴮ f)

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
        cases a, cases a_right, cases a_left, solve_by_elim }, simp only [le_inf_iff] at a,
        cases a, cases a_right, cases a_left, solve_by_elim },

    rw[β₁_property] at a_left_right,
    have H_le_eq : Γ ≤ ((η₂.func β₁_val)̌ ) =ᴮ ((η₂.func β₂_val)̌ ),
     by {apply eq_of_is_func_of_eq, from a_right_left, tactic.rotate 1,
         from ‹_›, from ‹_›, from bv_refl },
    from le_trans H_le_eq
           (by {rw[le_bot_iff], apply check_bv_eq_bot_of_not_equiv, apply H_inj₂, tidy})},
   intro H_CCC, specialize H_CCC (g⁻¹'{ξ}) ‹_› ‹_› ‹_›,
   replace H_ξ := (lt_iff_le_and_ne.mp H_ξ),
   from absurd (le_antisymm H_ξ.left H_CCC) H_ξ.right
end

end cardinal_preservation
end bSet

open bSet

namespace pSet

@[reducible]noncomputable def ℵ₁ : pSet.{0} := ordinal.mk (aleph 1).ord

@[reducible]noncomputable def ℵ₂ : pSet.{0} := ordinal.mk (aleph 2).ord

lemma ℵ₂_unfold : ℵ₂ = ⟨ℵ₂.type, ℵ₂.func⟩ := by cases ℵ₂; refl

@[simp, cleanup]lemma Union_type {x : pSet} : (type (Union x)) = Σ(a:x.type), (x.func a).type :=
by induction x; refl

@[simp, cleanup]lemma Union_type' {α : Type u} {A : α → pSet.{u}} :
  (Union (mk α A)).type = Σa, (A a).type := rfl

end pSet

open pSet

def 𝔹_cohen : Type := @regular_opens (set(ℵ₂.type × ℕ)) (Pi.topological_space)

local notation `𝔹` := 𝔹_cohen

instance H_nonempty : nonempty (set $ ℵ₂.type × ℕ) := ⟨∅⟩

@[instance, priority 1000]def 𝔹_boolean_algebra : nontrivial_complete_boolean_algebra 𝔹 :=
regular_open_algebra

lemma le_iff_subset' {x y : 𝔹} : x ≤ y ↔ x.1 ⊆ y.1 := by refl

lemma bot_eq_empty : (⊥ : 𝔹) = ⟨∅, is_regular_empty⟩ := rfl

private lemma eq₀ : (ℵ₂̌  : bSet 𝔹).type = (ℵ₂).type := by cases ℵ₂; refl

private lemma eq₁ : ((type (ℵ₂̌  : bSet 𝔹)) × ℕ) = ((type ℵ₂) × ℕ) :=
by {cases ℵ₂, refl}

private lemma eq₂ : set ((type (ℵ₂̌  : bSet 𝔹)) × ℕ) = set ((type ℵ₂) × ℕ) :=
by {cases ℵ₂, refl}

private lemma eq₃ : finset ((type (ℵ₂̌  : bSet 𝔹)) × ℕ) = finset (type ℵ₂ × ℕ) :=
by {cases ℵ₂, refl}

lemma pi₂_cast₁ {α β γ : Type*} (H' : α = β) {p : α × γ} {q : β × γ} (H : p == q) :
  p.1 == q.1 :=
by {subst H', subst H}

lemma pi₂_cast₂ {α β γ : Type*} (H' : α = β) {p : α × γ} {q : β × γ} (H : p == q) :
  p.2 = q.2 :=
by {subst H', subst H}

lemma compl_cast₂ {α β : Type*} {a : set α} {b : set β} (H' : α = β) (H : -a == b) : a == -b :=
begin
  subst H', subst H, apply heq_of_eq, simp
end

lemma eq₁_cast (p : ((type (ℵ₂̌  : bSet 𝔹)) × ℕ)) {prf : ((type (ℵ₂̌  : bSet 𝔹)) × ℕ) = (((type ℵ₂) × ℕ))} {prf' : (type (ℵ₂̌  : bSet 𝔹)) = (ℵ₂.type)} : cast prf p = (cast prf' p.1, p.2) :=
begin
  ext, swap, simp, h_generalize H_x : p == x, apply pi₂_cast₂, from eq₀.symm, from H_x.symm,
  h_generalize H_x : p == x, simp, h_generalize H_y : p.fst == y,
  apply eq_of_heq, suffices : x.fst == p.fst, from heq.trans this H_y,
  apply pi₂_cast₁, from eq₀.symm, from H_x.symm
end

lemma eq₁_cast' (p : (((type ℵ₂) × ℕ))) {prf : ((type (ℵ₂̌  : bSet 𝔹)) × ℕ) = (((type ℵ₂) × ℕ))} {prf' : (type (ℵ₂̌  : bSet 𝔹)) = (ℵ₂.type)} : cast prf.symm p = (cast prf'.symm p.1, p.2) :=
begin
  ext, swap, simp, h_generalize H_x : p == x, apply pi₂_cast₂, from eq₀, from H_x.symm,
  h_generalize H_x : p == x, simp, h_generalize H_y : p.fst == y,
  apply eq_of_heq, suffices : x.fst == p.fst, from heq.trans this H_y,
  apply pi₂_cast₁, from eq₀, from H_x.symm
end

theorem 𝔹_CCC : CCC 𝔹 :=
by { apply CCC_regular_opens, apply cantor_space.countable_chain_condition_set }

local notation `𝒳` := set(ℵ₂.type × ℕ)

open topological_space

/-- The principal regular open associated to a pair (ν, n) is the collection of all subsets of
    ℵ₂ × ℕ which contain (ν, n). -/
def principal_open (ν : (ℵ₂̌  : bSet 𝔹).type) (n : ℕ) : 𝔹 :=
begin
  use (cantor_space.principal_open (cast eq₁ (ν, n))),
  from is_regular_of_clopen (cantor_space.is_clopen_principal_open)
end

lemma is_clopen_principal_open {ν n} : is_clopen (principal_open ν n).val :=
  cantor_space.is_clopen_principal_open

local postfix `ᵖ`:80 := perp

local notation `cl`:65 := closure

local notation `int`:65 := interior

lemma perp_eq_compl_of_clopen {β : Type*} [topological_space β] {S : set β} (H : is_clopen S) : Sᵖ = (-S) :=
by {unfold perp, rw[closure_eq_of_is_closed H.right]}

lemma mem_neg_principal_open_of_not_mem {ν n S} : (cast eq₁ (ν,n) ∈ (-S)) → S ∈ (- (principal_open ν n)).val :=
begin
  intro H, simp only [neg_unfold], rw[perp_eq_compl_of_clopen],
  swap, from is_clopen_principal_open, from H
end

structure 𝒞 : Type :=
(ins : finset ((ℵ₂ ̌ : bSet 𝔹).type × ℕ))
(out : finset ((ℵ₂ ̌ : bSet 𝔹).type × ℕ))
(H : ins ∩ out = ∅)

@[reducible]def π₂ : (ℵ₂̌  : bSet 𝔹).type × ℕ → ℕ := λ x, x.snd

-- def nat_supp : finset ((ℵ₂ ̌ : bSet 𝔹).type × ℕ) → set ℕ :=
-- λ X, {n | ∃ (ξ : ℵ₂.type), (cast eq₁.symm (ξ,n)) ∈ X}

-- lemma nat_supp_finite {X} : set.finite $ nat_supp X := sorry

private def ι : 𝒞 → 𝔹 :=
λ p, ⟨{S | (p.ins.to_set) ⊆ (cast eq₂.symm S) ∧
           (p.out.to_set) ⊆ (cast eq₂.symm (- S))},
is_regular_of_clopen
     begin
       change is_clopen
         ({S | p.ins.to_set ⊆ cast eq₂.symm S} ∩ {S | p.out.to_set ⊆ (cast eq₂.symm (-S))}),
       refine is_clopen_inter _ _,
         have := cantor_space.is_clopen_principal_open_finset p.ins,
         convert this, from eq₀.symm, from eq₀.symm, from eq₀.symm,
           {apply function.hfunext, from eq₂.symm, intros a a' H_heq,
             apply heq_of_eq, convert rfl, convert (cast_eq _ _).symm, from eq₀.symm, refl},

         have := cantor_space.is_clopen_co_principal_open_finset p.out,
         convert this, from eq₀.symm, from eq₀.symm, from eq₀.symm,
         {apply function.hfunext, from eq₂.symm, intros a a' H_heq,
          apply heq_of_eq, convert rfl, h_generalize Hx : (-a) == x,
          have := heq.subst H_heq, swap,
          from λ _ y, y == -x,
          suffices : a' = -x, by {rw[this], simp},
          apply eq_of_heq, apply this, apply compl_cast₂, from eq₁.symm,
          from Hx}
     end⟩

open cantor_space

lemma prop_decidable_cast_lemma {α β : Type*} (H : α = β) {a b : α} {a' b' : β} (H_a : a == a') (H_b : b == b') : classical.prop_decidable (a = b) == classical.prop_decidable (a' = b') :=
by {subst H, subst H_a, subst H_b}

lemma 𝒞_dense_basis : ∀ T ∈ @standard_basis (ℵ₂.type × ℕ), ∀ h_nonempty : T ≠ ∅,
  ∃ p : 𝒞, (ι p).val ⊆ T :=
begin
  intros T Ht H_nonempty, simp[standard_basis] at Ht,
  cases Ht with H_empty Ht, contradiction,
  rcases Ht with ⟨p_ins, p_out, H₁, H₂⟩,
  fsplit, refine ⟨_,_,_⟩, from cast eq₃.symm p_ins,
  from cast eq₃.symm p_out, swap, rw[<-co_principal_open_finset_eq_inter] at H₁,
  rw[<-principal_open_finset_eq_inter] at H₁, subst H₁,
  intros S HS, split, cases HS, dsimp at HS_left, simp[principal_open_finset],
  {convert HS_left,
    from eq₀.symm, from eq₀.symm, from eq₀.symm, all_goals{symmetry, from cast_heq _ _}},
  cases HS, dsimp at HS_right, simp[principal_open_finset],
  {convert HS_right,
    from eq₀.symm, from eq₀.symm, from eq₀.symm, all_goals{symmetry, from cast_heq _ _}},
  convert H₂, from eq₀, from eq₀, from eq₀,
  apply function.hfunext, from eq₁, intros a a' H,
  apply function.hfunext, from eq₁, intros b b' H',
  from prop_decidable_cast_lemma eq₁ ‹_› ‹_›,
  from cast_heq _ _, from cast_heq _ _, from eq₀, from eq₀
end

lemma 𝒞_dense {b : 𝔹} (H : ⊥ < b) : ∃ p : 𝒞, (ι p) ≤ b :=
begin
  cases (classical.choice (classical.nonempty_of_not_empty _ H.right.symm)) with S_wit H_wit,
  change ∃ p, (ι p).val ⊆ b.val,
  have := mem_basis_subset_of_mem_open (is_topological_basis_standard_basis) H_wit (is_open_of_is_regular b.property),
  rcases (mem_basis_subset_of_mem_open
           (is_topological_basis_standard_basis) H_wit (is_open_of_is_regular b.property))
         with ⟨v, Hv₁, Hv₂, Hv₃⟩,
  have : v ≠ ∅, by {intro H, rw[H] at Hv₂, cases Hv₂},
  cases (𝒞_dense_basis ‹_› ‹_› ‹_›) with p H_p, from ⟨p, set.subset.trans H_p ‹_›⟩
end

lemma to_set_inter {α : Type*} {p₁ p₂ : finset α} : (p₁ ∩ p₂).to_set = (p₁.to_set ∩ p₂.to_set) :=
by {ext, split; intros; unfold finset.to_set at *, tidy}

@[simp]lemma to_set_empty {α : Type*} : finset.to_set (∅ : finset α) = ∅ :=
by {unfold finset.to_set, refl}

lemma not_mem_of_inter_empty_left {α : Type*} {p₁ p₂ : finset α}
  (H : p₁ ∩ p₂ = ∅) {a : α} : a ∈ p₁.to_set → ¬ a ∈ p₂.to_set :=
begin
  intro H', intro H'',
  have this₀ : a ∈ p₁.to_set ∩ p₂.to_set := ⟨‹_›,‹_›⟩,
  rw[<-to_set_inter] at this₀, have this₁ := congr_arg finset.to_set H,
  rw[this₁] at this₀, cases this₀
end

lemma not_mem_of_inter_empty_right {α : Type*} {p₁ p₂ : finset α}
  (H : p₂ ∩ p₁ = ∅) {a : α} : a ∈ p₁.to_set → ¬ a ∈ p₂.to_set :=
by {rw[finset.inter_comm] at H, apply not_mem_of_inter_empty_left, from ‹_›}

lemma 𝒞_nonzero (p : 𝒞) : ⊥ ≠ (ι p) :=
begin
  intro H, replace H := H.symm, rw[eq_bot_iff] at H, rw[le_iff_subset'] at H,
  rw[bot_eq_empty] at H,
  suffices : nonempty (ι p).val,
    by {have := classical.choice this, specialize H this.property, cases H},
  apply nonempty.intro, fsplit, exact (cast eq₂ p.ins.to_set),
  split, finish, intro x, cases x with ν n, intro H,
  suffices : cast eq₁ (ν, n) ∈ - cast eq₂ (p.ins).to_set,
    {convert this, from eq₀, from eq₀, from eq₀, cc, cc},
  suffices : (ν, n) ∈ - p.ins.to_set,
    {convert this, from eq₀.symm, from eq₀.symm, from eq₀.symm, cc, from eq₀.symm,
     from eq₀.symm, from eq₀.symm, from eq₀.symm, cc},
  from not_mem_of_inter_empty_right p.H H
end

lemma subset_of_eq {α : Type*} {a b : finset α} (H : a = b) : a ⊆ b := by rw[H]; refl

lemma 𝒞_disjoint_row (p : 𝒞) : ∃ n : ℕ, ∀ ξ : ℵ₂.type, (cast eq₁.symm (ξ,n)) ∉ p.ins ∧ (cast eq₁.symm (ξ,n)) ∉ p.out :=
begin
  let Y := (finset.image π₂ p.ins) ∪ (finset.image π₂ p.out),
  by_cases (p.ins ∪ p.out) = ∅,
  use 0, intro ξ, split, intro x, apply (subset_of_eq h), simp, left, from x,
  intro x, apply (subset_of_eq h), simp, right, from x,
  let Y' := finset.image π₂ (p.ins ∪ p.out),
  have Y'_nonempty : Y' ≠ ∅,
    by {dsimp[Y'], intro H, apply h, ext; split; intros, swap, cases a_1,
      have : π₂ a ∈ finset.image π₂ (p.ins ∪ p.out), simp,
      use a.fst, simp at a_1, convert a_1, cases a, refl, cases a, refl,
      rw[H] at this, cases this},
  have := finset.max_of_ne_empty,
  specialize this Y'_nonempty, cases this with N HN, swap, apply_instance,
  use (N+1), intro ξ, split,
    intro X, let prf := _, change cast prf (ξ, N + 1) ∈ p.ins at X,
    rw[eq₁_cast'] at X, swap, from eq₀,
    have : N + 1 ∈ Y',
      by {simp, use cast eq₀.symm ξ, from or.inl X},
    suffices : N + 1 ≤ N, by {revert this, change ¬ (N + 1 ≤ N), apply nat.not_succ_le_self},
    apply finset.le_max_of_mem this ‹_›,
  intro X, let prf := _, change cast prf (ξ, N + 1) ∈ p.out at X,
    rw[eq₁_cast'] at X, swap, from eq₀,
    have : N + 1 ∈ Y',
      by {simp, use cast eq₀.symm ξ, from or.inr X},
    suffices : N + 1 ≤ N, by {revert this, change ¬ (N + 1 ≤ N), apply nat.not_succ_le_self},
    apply finset.le_max_of_mem this ‹_›
end

lemma 𝒞_anti {p₁ p₂ : 𝒞} : p₁.ins ⊆ p₂.ins → p₁.out ⊆ p₂.out → ι p₂ ≤ ι p₁  :=
by {intros H₁ H₂, rw[le_iff_subset'], tidy}

namespace cohen_real
section cohen_real

/-- `cohen_real.χ ν` is the indicator function on ℕ induced by every ordinal less than ℵ₂ -/
def χ (ν : (ℵ₂̌  : bSet 𝔹).type) : ℕ → 𝔹 :=
  λ n, principal_open ν n

/-- `cohen_real.mk ν` is the subset of (ω : bSet 𝔹) induced by `cohen_real.χ ν` -/
def mk (ν : (ℵ₂̌  : bSet 𝔹).type) : bSet 𝔹 :=
  @bSet.set_of_indicator 𝔹 _ omega $ λ n, χ ν n.down

@[simp, cleanup]lemma mk_type {ν} : (mk ν).type = ulift ℕ := rfl

@[simp, cleanup]lemma mk_func {ν} {n} : (mk ν).func n = bSet.of_nat (n.down) := rfl

@[simp, cleanup]lemma mk_bval {ν} {n} : (mk ν).bval n = (χ ν) (n.down) := rfl

/-- bSet 𝔹 believes that each `mk ν` is a subset of omega -/
lemma definite {ν} {Γ} : Γ ≤ mk ν ⊆ᴮ omega :=
by simp [mk, subset_unfold]; from λ _, by rw[<-deduction]; convert omega_definite

/-- bSet 𝔹 believes that each `mk ν` is an element of 𝒫(ω) -/
lemma definite' {ν} {Γ} : Γ ≤ mk ν ∈ᴮ bv_powerset omega := bv_powerset_spec.mp definite

lemma sep {n} {Γ} {ν₁ ν₂} (H₁ : Γ ≤ (of_nat n) ∈ᴮ (mk ν₁)) (H₂ : Γ ≤ (- ((of_nat n) ∈ᴮ (mk ν₂)))) :
  Γ ≤ (- ((mk ν₁) =ᴮ (mk ν₂))) :=
begin
  rw[bv_eq_unfold], rw[neg_inf, neg_infi, neg_infi], simp only [lattice.neg_imp],
  refine le_sup_left_of_le _, rw[@bounded_exists 𝔹 _ (mk ν₁) (λ z, -(z ∈ᴮ mk ν₂)) _],
  swap, change B_ext _, simp[-imp_bot, imp_bot.symm],
  apply bv_use (bSet.of_nat n), bv_split_goal
end

lemma not_mem_of_not_mem {p : 𝒞} {ν} {n} (H : (ν,n) ∈ p.out) : ι p ≤ -( (of_nat n) ∈ᴮ (mk ν)) :=
begin
rw[bSet.mem_unfold, neg_supr], bv_intro k, rw[neg_inf], simp,
       by_cases n = k.down, swap, rw[bSet.of_nat_inj ‹_›],
       from le_sup_right_of_le (by simp),
       refine le_sup_left_of_le _, rw[<-h],
       rw[le_iff_subset'], unfold ι χ, rintros S ⟨H_S₁, H_S₂⟩,
       apply mem_neg_principal_open_of_not_mem, have := H_S₂ H, convert this,
       from eq₀.symm, from eq₀.symm, from eq₀.symm,
       from cast_heq _ _, from (cast_heq _ _).symm
end

private lemma inj_cast_lemma (ν' : type (ℵ₂̌  : bSet 𝔹)) (n' : ℕ) :
  cast eq₁.symm (cast eq₀ ν', n') = (ν', n') :=
begin
  let a := _, change cast a _ = _,
  let b := _, change cast _ (cast b _, _) = _,
  simp[b] at a, dedup, change cast a_1 _ = _, cc
end

/-- Whenever ν₁ ≠ ν₂ < ℵ₂, bSet 𝔹 believes that `mk ν₁` and `mk ν₂` are distinct -/
lemma inj {ν₁ ν₂} (H_neq : ν₁ ≠ ν₂) : (mk ν₁) =ᴮ (mk ν₂) ≤ (⊥ : 𝔹) :=
begin
  by_contra, replace h := (bot_lt_iff_not_le_bot.mpr ‹_›),
  cases 𝒞_dense h with p H_p, cases 𝒞_disjoint_row p with n H_n,
  let p' : 𝒞 := { ins := insert (ν₁,n) (p.ins),
  out := insert (ν₂,n) p.out,
  H := by {ext, split; intro H, swap, cases H, have := p.H, simp at H, cases a_1 with ν' n',
           cases H with H₁ H₂, specialize H_n (cast eq₀ ν'), cases H_n, cases H₁; cases H₂, cc,
           exfalso, apply H_n_right, convert H₂, rw[show n = n', by cc], apply inj_cast_lemma,
           exfalso, apply H_n_left, convert H₁, rw[show n = n', by cc], apply inj_cast_lemma,
           rw[<-this], simp[*,-this]} },
  have this₀ : ι p' ≤ ι p,
    from 𝒞_anti (by {dsimp[p'], from λ i _, by {simp, from or.inr ‹_›}})
                (by {dsimp[p'], from λ i _, by {simp, from or.inr ‹_›}}),
  have this₁ : ι p' ≤ (ñ̌) ∈ᴮ (cohen_real.mk ν₁),
    by {rw[bSet.mem_unfold], apply bv_use (ulift.up n), refine le_inf _ bv_refl,
         {simp [le_iff_subset', χ, _root_.principal_open, ι, cantor_space.principal_open],
         have : (ν₁, n) ∈ p'.ins,
           by simp[p'], intros S H_S _, specialize H_S this,
              convert H_S; [from eq₀.symm, from eq₀.symm, from eq₀.symm, cc, cc]}},
  have this₂ : ι p' ≤ - ((ñ̌) ∈ᴮ (cohen_real.mk ν₂)),
    by {have : (ν₂, n) ∈ p'.out, by {simp[p']},
       from not_mem_of_not_mem ‹_›},
  have this₃ : ι p' ≤ - (mk ν₁ =ᴮ mk ν₂),
    from sep ‹_› ‹_›,
  have this₄ : ι p' ≤ (mk ν₁ =ᴮ mk ν₂),
    from le_trans this₀ ‹_›,
  suffices : ι p' = ⊥, from absurd this.symm (𝒞_nonzero p'),
  bv_and_intro this₃ this₄, simpa using H
end

end cohen_real
end cohen_real

section neg_CH

local attribute [irreducible] regular_opens 𝔹_cohen

local notation `ℵ₀` := (omega : bSet 𝔹)
local notation `𝔠` := (bv_powerset ℵ₀ : bSet 𝔹)

lemma uncountable_fiber_of_regular' (κ₁ κ₂ : cardinal) (H_inf : cardinal.omega ≤ κ₁) (H_lt : κ₁ < κ₂) (H : cof (ord κ₂) = κ₂) (α : Type u) (H_α : #α = κ₁) (β : Type u) (H_β : #β = κ₂) (g : β → α)
  : ∃ (ξ : α), cardinal.omega < #↥(g⁻¹' {ξ}) :=
begin
  have := (@cardinal.exists_aleph κ₂).mp (le_of_lt (lt_of_le_of_lt ‹_› ‹_›)), cases this with k H_k, subst H_k,
  have := (@cardinal.exists_aleph κ₁).mp ‹_›, cases this with k' H_k', subst H_k',
  have := infinite_pigeonhole g _ _, cases this with ξ H_ξ, use ξ, rw[H_ξ],
  all_goals{simp*}, from lt_of_le_of_lt ‹_› ‹_›
end

lemma uncountable_fiber_of_regular (κ₁ κ₂ : cardinal) (H_inf : cardinal.omega ≤ κ₁) (H_lt : κ₁ < κ₂) (H : cof (ord κ₂) = κ₂) (g : type (pSet.ordinal.mk (ord κ₂)  : pSet.{u}) → type (pSet.ordinal.mk (ord κ₁) : pSet.{u}))
  : ∃ (ξ : type (pSet.ordinal.mk (ord κ₁))), cardinal.omega < #↥((λ (β : type (pSet.ordinal.mk (ord κ₂))), g β)⁻¹' {ξ}) :=
begin
  have := (@exists_aleph κ₁).mp ‹_›, cases this with k₁ h, subst h,
  have := (@exists_aleph κ₂).mp (le_of_lt (lt_of_le_of_lt ‹_› ‹_›)), cases this with k₂ h,
  subst h,
  from uncountable_fiber_of_regular' (aleph k₁) (aleph k₂) ‹_› ‹_› ‹_› _ (by simp) _ (by simp) g
end

lemma cardinal_inequality_of_regular (κ₁ κ₂ : cardinal) (H_reg₁ : cardinal.is_regular κ₁) (H_reg₂ : cardinal.is_regular κ₂) (H_inf : (omega : cardinal) ≤ κ₁) (H_lt : κ₁ < κ₂) {Γ : 𝔹} : Γ ≤ (card_ex κ₁)̌  ≺ (card_ex κ₂)̌  :=
begin
  dsimp only, rw ←imp_bot, bv_imp_intro H_larger_than,
  by_contra H_nonzero, rw ←bot_lt_iff_not_le_bot at H_nonzero,
  rcases AE_of_check_larger_than_check H_nonzero ‹_› (exists_mem_of_regular ‹_›) with ⟨f,Hf⟩,
  rcases classical.axiom_of_choice Hf with ⟨g, g_spec⟩,
    suffices : ¬ CCC 𝔹, from absurd 𝔹_CCC this,
    apply not_CCC_of_uncountable_fiber; try{assumption},
    {have := (@cardinal.exists_aleph κ₁).mp ‹_›, cases this with k' H_k', subst H_k', simp*},
    {have := (@cardinal.exists_aleph κ₁).mp ‹_›, cases this with k' H_k', subst H_k', simp*,
     have := (@exists_aleph κ₂).mp (le_of_lt (lt_of_le_of_lt ‹_› ‹_›)), cases this with k₂ h,
     subst h, simp*},
    {intros i₁ i₂ H_neq, from ordinal.mk_inj _ _ _ ‹_›},
    {dsimp at g,
     apply uncountable_fiber_of_regular' κ₁ κ₂; try{simp*},
     from H_reg₂.right,
     have := (@exists_aleph κ₂).mp (le_of_lt (lt_of_le_of_lt ‹_› ‹_›)), cases this with k₂ h,
     subst h; apply mk_type_mk_eq, from ‹_›, apply mk_type_mk_eq,
     from le_of_lt (lt_of_le_of_lt ‹_› ‹_›)}
end

lemma ℵ₀_lt_ℵ₁ : (⊤ : 𝔹)  ≤ ℵ₀ ≺ ℵ₁̌  :=
begin
  dsimp only, rw ←imp_bot, bv_imp_intro H_larger_than,
  by_contra H_nonzero, rw ←bot_lt_iff_not_le_bot at H_nonzero,
  rcases AE_of_check_larger_than_check ‹_› ‹_› _ with ⟨f,Hf⟩,
  rcases (classical.axiom_of_choice Hf) with ⟨g,g_spec⟩,
  suffices : ¬ CCC 𝔹, from absurd 𝔹_CCC this,
  apply not_CCC_of_uncountable_fiber; try{assumption},
    {from le_of_eq (by simp)},
    {simp},
    {intros i₁ i₂ H_neq, from ordinal.mk_inj _ _ _ ‹_›},
    {dsimp at g,
     apply uncountable_fiber_of_regular' (aleph 0) (aleph 1); try{simp*},
     from is_regular_aleph_one.right},
  from exists_mem_of_regular is_regular_aleph_one
end


lemma ℵ₁_lt_ℵ₂ : (⊤ : 𝔹) ≤ ℵ₁̌  ≺ ℵ₂̌  :=
cardinal_inequality_of_regular _ _ (is_regular_aleph_one)
  (is_regular_aleph_two) (by simp) (by simp)

lemma ℵ₁_lt_ℵ₂' {Γ : 𝔹} : Γ ≤ ℵ₁̌  ≺ ℵ₂̌  := le_trans (le_top) ℵ₁_lt_ℵ₂

lemma cohen_real.mk_ext : ∀ (i j : type (ℵ₂̌  : bSet 𝔹)), func (ℵ₂̌ ) i =ᴮ func (ℵ₂̌ ) j ≤
  (λ (x : type (ℵ₂̌ )), cohen_real.mk x) i =ᴮ (λ (x : type (ℵ₂̌ )), cohen_real.mk x) j :=
begin
  intros i j, by_cases i = j,
   {simp[h]},
   {refine poset_yoneda _, intros Γ a, simp only [le_inf_iff] at *,
     have : func (ℵ₂̌ ) i = (ℵ₂.func (check_cast i))̌ ,
       by simp[check_func],
     rw[this] at a,
     have : func (ℵ₂̌ ) j = (ℵ₂.func (check_cast j))̌ ,
       by simp[check_func],
     rw[this] at a,
   suffices : (ℵ₂.func (check_cast i))̌   =ᴮ (ℵ₂.func (check_cast j))̌  ≤ ⊥,
     from le_trans a (le_trans this bot_le),
   rw[le_bot_iff], apply check_bv_eq_bot_of_not_equiv,
   apply ordinal.mk_inj, unfold check_cast, intro H, cc}
end

noncomputable def neg_CH_func : bSet 𝔹 :=
@function.mk _ _ (ℵ₂̌ ) (λ x, cohen_real.mk x) cohen_real.mk_ext

theorem ℵ₂_le_𝔠 : ⊤ ≤ is_func' (ℵ₂̌ ) 𝔠 (neg_CH_func) ⊓ bSet.is_inj (neg_CH_func) :=
begin
refine le_inf _ _,

  {unfold neg_CH_func, refine le_inf _ _, refine mk_is_func _ _,
    bv_intro w₁, bv_imp_intro, rw[bSet.mem_unfold] at H,
    bv_cases_at'' H ν, apply bv_use (cohen_real.mk ν),
    refine le_inf cohen_real.definite' _, swap,
    rw[bSet.mem_unfold], apply bv_use ν, bv_split,
    from le_inf ‹_› (by apply le_trans H_1_right; from subst_congr_pair_left)},

  {refine mk_inj_of_inj _ _, from λ _ _ _, cohen_real.inj ‹_›},
end

theorem neg_CH : (⊤ : 𝔹) ≤ -CH :=
begin
  dsimp [CH], rw[lattice.neg_neg], apply bv_use (ℵ₁̌ ),
  apply bv_use (ℵ₂̌ ), simp only [lattice.le_inf_iff],
  refine ⟨⟨ℵ₀_lt_ℵ₁, ℵ₁_lt_ℵ₂⟩, bv_use neg_CH_func⟩,
  from ℵ₂_le_𝔠
end

def CH' : 𝔹 := - ⨆ x, (ℵ₀ ≺ x) ⊓ (x ≺ 𝒫(ℵ₀))

theorem neg_CH' : ⊤ ≤ -CH' :=
begin
  have := neg_CH, unfold CH at this,
  erw lattice.neg_neg at this ⊢, bv_cases_at this x Hx,
  bv_cases_at Hx y Hy,
  apply bv_use x, bv_split_at Hy, bv_split_at Hy_left,
  refine le_inf ‹_› _, refine bSet_lt_of_lt_of_le _ _ _ _ _,
  tactic.rotate 2, exact Hy_right, exact Hy_left_right
end

end neg_CH
