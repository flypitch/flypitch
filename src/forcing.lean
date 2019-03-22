import .bvm_extras .pSet_ordinal .set_theory .regular_open_algebra

open ordinal cardinal lattice bSet

noncomputable theory

local attribute [instance] classical.prop_decidable

local attribute [simp] omega_le_aleph

local infix ` ⟹ `:65 := lattice.imp

local infix ` ⇔ `:50 := lattice.biimp

local prefix `#`:70 := cardinal.mk

universe u

namespace bSet
section cardinal_preservation
local notation `ω` := cardinal.omega
variables {𝔹 : Type u} [I : nontrivial_complete_boolean_algebra 𝔹]

include I
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

-- @[reducible]def is_regular_open : set (set(ℵ₂.type × ℕ)) → Prop := -- is_regular
-- sorry

def 𝔹 : Type := @regular_opens (set(ℵ₂.type × ℕ)) (Pi.topological_space)
-- {s // is_regular_open S}

instance H_nonempty : nonempty (set $ ℵ₂.type × ℕ) := ⟨∅⟩

@[instance, priority 1000]def 𝔹_boolean_algebra : nontrivial_complete_boolean_algebra 𝔹 :=
regular_open_algebra (H_nonempty)


lemma le_iff_subset' {x y : 𝔹} : x ≤ y ↔ x.1 ⊆ y.1 := by refl

lemma bot_eq_empty : (⊥ : 𝔹) = ⟨∅, is_regular_empty⟩ := rfl

private lemma eq₀ : (ℵ₂̌  : bSet 𝔹).type = (ℵ₂).type := by cases ℵ₂; refl

private lemma eq₁ : ((type (ℵ₂̌  : bSet 𝔹)) × ℕ) = ((type ℵ₂) × ℕ) :=
by {cases ℵ₂, refl}

private lemma eq₂ : set ((type (ℵ₂̌  : bSet 𝔹)) × ℕ) = set ((type ℵ₂) × ℕ) :=
by {cases ℵ₂, refl}

-- lemma 𝔹'_cast : (set (type ℵ₂ × ℕ)) = (set ((ℵ₂̌  : bSet 𝔹').type × ℕ)) :=
--   by {cases (ℵ₂), refl}

-- lemma 𝔹'_cast_set : set (set (type ℵ₂ × ℕ)) = set (set ((ℵ₂̌  : bSet 𝔹').type × ℕ)) :=
--   by {cases (ℵ₂), refl}

-- def is_regular_open' : set (set ((ℵ₂ ̌).type × ℕ)) → Prop :=
-- λ S, is_regular_open (cast 𝔹'_cast_set.symm S)

-- def 𝔹 : Type := {S // is_regular_open' S}

-- instance 𝔹_boolean_algebra : nontrivial_complete_boolean_algebra 𝔹 := sorry

theorem 𝔹_CCC : CCC 𝔹 := sorry 

/-- The principal regular open associated to a pair (ν, n) is the collection of all subsets of
    ℵ₂ × ℕ which contain (ν, n). -/
def principal_open (ν : (ℵ₂̌  : bSet 𝔹).type) (n : ℕ) : 𝔹 :=
begin
  use {S | cast eq₁ (ν, n) ∈ S},
  {sorry}
end

lemma neg_principal_open {ν n} {S} : S ∈ (- (principal_open ν n)).val ↔ (cast eq₁ (ν,n) ∈ (-S))
:= sorry

-- #check (by apply_instance : has_inter $ finset ((ℵ₂ ̌ : bSet 𝔹).type × ℕ))

structure 𝒞 : Type :=
(ins : finset ((ℵ₂ ̌ : bSet 𝔹).type × ℕ))
(out : finset ((ℵ₂ ̌ : bSet 𝔹).type × ℕ))
(H : ins ∩ out = ∅)

--((ins ∩ out) : finset ((ℵ₂ ̌ : bSet 𝔹).type × ℕ)) = (∅ : finset ((ℵ₂ ̌ : bSet 𝔹).type × ℕ)

-- instance : has_insert ((ℵ₂ ̌).type × ℕ) 𝒞 := ⟨by {dsimp[𝒞], exact insert}⟩

def ι : 𝒞 → 𝔹 :=
λ p, ⟨{S | (p.ins.to_set) ⊆ (cast eq₂.symm S) ∧
           (p.out.to_set) ⊆ (cast eq₂.symm (- S))}, sorry⟩

lemma 𝒞_dense {b : 𝔹} (H : ⊥ < b) : ∃ p : 𝒞, ι p ≤ b := sorry 
-- TODO(jesse) use that b is open, b is a union of basis elements,
-- and 𝒞 is dense for the basis elements

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

lemma 𝒞_disjoint_row (p : 𝒞) : ∃ n : ℕ, ∀ ξ : ℵ₂.type, (cast eq₁.symm (ξ,n)) ∉ p.ins ∧ (cast eq₁.symm (ξ,n)) ∉ p.out :=
sorry

lemma 𝒞_anti {p₁ p₂ : 𝒞} : p₁.ins ⊆ p₂.ins → p₁.out ⊆ p₂.out → ι p₂ ≤ ι p₁  :=
by {intros H₁ H₂, rw[le_iff_subset'], tidy}

namespace cohen_real

/-- `cohen_real.χ ν` is the indicator function on ℕ induced by every ordinal less than ℵ₂ -/
def χ (ν : (ℵ₂̌  : bSet 𝔹).type) : ℕ → 𝔹 :=
  λ n, principal_open ν n

/-- `cohen_real.mk ν` is the subset of (ω : bSet 𝔹) induced by `cohen_real.χ ν` -/
def mk (ν : (ℵ₂̌  : bSet 𝔹).type) : bSet 𝔹 :=
  @set_of_indicator 𝔹 _ omega $ λ n, χ ν n.down

@[simp, cleanup]lemma mk_type {ν} : (mk ν).type = ulift ℕ := rfl

@[simp, cleanup]lemma mk_func {ν} {n} : (mk ν).func n = bSet.of_nat (n.down) := rfl

@[simp, cleanup]lemma mk_bval {ν} {n} : (mk ν).bval n = (χ ν) (n.down) := rfl

/-- bSet 𝔹 believes that each `mk ν` is a subset of omega -/
lemma definite {ν} {Γ} : Γ ≤ mk ν ⊆ᴮ omega :=
by simp [mk, subset_unfold]; from λ _, by rw[<-deduction]; convert omega_definite

/-- bSet 𝔹 believes that each `mk ν` is an element of 𝒫(ω) -/
lemma definite' {ν} {Γ} : Γ ≤ mk ν ∈ᴮ bv_powerset omega := bv_powerset_spec.mp definite

-- TODO(jesse) refactor this proof to use axiom of extensionality instead, or prove a more general version

lemma sep {n} {Γ} {ν₁ ν₂} (H₁ : Γ ≤ (of_nat n) ∈ᴮ (mk ν₁)) (H₂ : Γ ≤ (- ((of_nat n) ∈ᴮ (mk ν₂)))) :
  Γ ≤ (- ((mk ν₁) =ᴮ (mk ν₂))) :=
begin
  rw[bv_eq_unfold], rw[neg_inf, neg_infi, neg_infi], simp only [neg_imp],
  apply le_sup_left_of_le, rw[@bounded_exists 𝔹 _ (mk ν₁) (λ z, -(z ∈ᴮ mk ν₂)) _],
  swap, change B_ext _, simp[-imp_bot, imp_bot.symm],
  apply bv_use (bSet.of_nat n), bv_split_goal
end

lemma not_mem_of_not_mem {p : 𝒞} {ν} {n} (H : (ν,n) ∈ p.out) : ι p ≤ -( (of_nat n) ∈ᴮ (mk ν)) :=
begin
rw[mem_unfold, neg_supr], bv_intro k, rw[neg_inf], simp,
       by_cases n = k.down, swap, rw[bSet.of_nat_inj ‹_›],
       from le_sup_right_of_le (by simp),
       apply le_sup_left_of_le, rw[<-h],
       rw[le_iff_subset'], unfold ι χ principal_open, rintros S ⟨H_S₁, H_S₂⟩,
       apply neg_principal_open.mpr, have := H_S₂ H, convert this,
       from eq₀.symm, from eq₀.symm, from eq₀.symm, cc, cc
end

private lemma inj_cast_lemma (ν' : type (ℵ₂̌  : bSet 𝔹)) (n' : ℕ) :
  cast eq₁.symm (cast eq₀ ν', n') = (ν', n') :=
begin
  let a := _, change cast a _ = _,
  let b := _, change cast _ (cast b _, _) = _,
  simp[b] at a, dedup, change cast a_1 _ = _, cc
end

/-- Whenever ν₁ ≠ ν₂ < ℵ₂, bSet 𝔹 believes that `mk ν₁` and `mk ν₂` are distinct -/
lemma inj {ν₁ ν₂} (H_neq : ν₁ ≠ ν₂) : (mk ν₁) =ᴮ (mk ν₂) ≤ ⊥ :=
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
    by {rw[mem_unfold], apply bv_use (ulift.up n), refine le_inf _ bv_eq_refl',
         {simp[le_iff_subset', χ, principal_open, ι],
         have : (ν₁, n) ∈ p'.ins,
           by simp[p'], intros S H_S H_S',
           specialize H_S this, convert H_S;
           [from eq₀.symm,from eq₀.symm,from eq₀.symm,cc,cc]}},
  have this₂ : ι p' ≤ - ((ñ̌) ∈ᴮ (cohen_real.mk ν₂)),
    by {have : (ν₂, n) ∈ p'.out, by {simp[p']},
       from not_mem_of_not_mem ‹_›},
  have this₃ : ι p' ≤ - (mk ν₁ =ᴮ mk ν₂),
    from sep ‹_› ‹_›,
  have this₄ : ι p' ≤ (mk ν₁ =ᴮ mk ν₂),
    from le_trans this₀ ‹_›,
  suffices : ι p' = ⊥, from (not_and_self _).mp ⟨(𝒞_nonzero p'), this.symm⟩,
  bv_and_intro this₃ this₄, simpa using H
end

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

noncomputable def neg_CH_func : bSet 𝔹 :=
@function.mk _ _ (ℵ₂̌ ) (λ x, cohen_real.mk x) cohen_real.mk_ext

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
