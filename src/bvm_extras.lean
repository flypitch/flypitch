/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
import .bvm .pSet_ordinal

open lattice

universe u

local infix ` ⟹ `:65 := lattice.imp

local infix ` ⇔ `:50 := lattice.biimp

local prefix `p𝒫`:65 := pSet.powerset

namespace bSet

section extras
variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

@[simp, cleanup]lemma insert1_bval_none {u v : bSet 𝔹} : (bSet.insert1 u ({v})).bval none  = ⊤ :=
by refl

@[simp, cleanup]lemma insert1_bval_some {u v : bSet 𝔹} {i} : (bSet.insert1 u {v}).bval (some i) = (bval {v}) i :=
by refl

@[simp, cleanup]lemma insert1_func_none {u v : bSet 𝔹} : (bSet.insert1 u ({v})).func none  = u :=
by refl

@[simp, cleanup]lemma insert1_func_some {u v : bSet 𝔹} {i} : (bSet.insert1 u ({v})).func (some i) = (func {v}) i :=
by refl

@[simp]lemma mem_singleton {x : bSet 𝔹} : ⊤ ≤ x ∈ᴮ {x} :=
by {rw[mem_unfold], apply bv_use none, unfold singleton, simp}

lemma eq_of_mem_singleton' {x y : bSet 𝔹} : y ∈ᴮ {x} ≤ x =ᴮ y :=
by {rw[mem_unfold], apply bv_Or_elim, intro i, cases i, simp[bv_eq_symm], repeat{cases i}}

lemma eq_of_mem_singleton {x y : bSet 𝔹} {c : 𝔹} (h : c ≤ y ∈ᴮ {x}) : c ≤ x =ᴮ y :=
le_trans h (by apply eq_of_mem_singleton')

lemma eq_mem_singleton {x y : bSet 𝔹} {Γ : 𝔹} : Γ ≤ y ∈ᴮ {x} → Γ ≤ y =ᴮ x :=
λ _, bv_symm $ eq_of_mem_singleton ‹_›

lemma eq_zero_of_mem_one {x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ x ∈ᴮ 1 → Γ ≤ x =ᴮ 0 :=
begin
  intro H_mem,
  suffices : Γ ≤ x ∈ᴮ {0},
    by exact eq_mem_singleton this,
  apply bv_rw' (bv_symm one_eq_singleton_zero), simpa
end

lemma mem_singleton_of_eq {x y : bSet 𝔹} {c : 𝔹} {h : c ≤ x =ᴮ y} : c ≤ y ∈ᴮ {x} :=
begin
  unfold singleton, unfold has_insert.insert,
  rw[mem_insert], simp, apply le_sup_left_of_le, rwa[bv_eq_symm]
end

lemma eq_inserted_of_eq_singleton {x y z : bSet 𝔹} : {x} =ᴮ bSet.insert1 y {z} ≤ x =ᴮ y :=
begin
  rw[bv_eq_unfold], apply bv_specialize_left none, apply bv_specialize_right none,
  unfold singleton, simp, rw[inf_sup_right], apply bv_or_elim,
  apply inf_le_left, apply inf_le_right_of_le, simp[eq_of_mem_singleton']
end

lemma insert1_symm (y z : bSet 𝔹) : ⊤ ≤ bSet.insert1 y {z} =ᴮ bSet.insert1 z {y} :=
begin
  rw[bv_eq_unfold], apply le_inf; bv_intro i; simp; cases i; simp[-top_le_iff],
  {simp[bv_or_right]},
  {cases i; [simp, repeat{cases i}]},
  {simp[bv_or_right]},
  {cases i; [simp, repeat{cases i}]}
end

lemma eq_inserted_of_eq_singleton' {x y z : bSet 𝔹} : {x} =ᴮ bSet.insert1 y {z} ≤ x =ᴮ z :=
by {apply bv_have_true (insert1_symm y z), apply le_trans, apply bv_eq_trans, apply eq_inserted_of_eq_singleton}

def binary_union (x y : bSet 𝔹) : bSet 𝔹 := bv_union {x,y}

-- note: maybe it's better to define this as a fiber product with a coherency condition?
def binary_inter (x y : bSet 𝔹) : bSet 𝔹 := ⟨x.type, x.func, λ i, x.bval i ⊓ (x.func i) ∈ᴮ y⟩

infix ` ∩ᴮ `:81 := _root_.bSet.binary_inter

@[simp, cleanup] lemma binary_inter_bval {x y : bSet 𝔹} {i : x.type} : (x ∩ᴮ y).bval i = x.bval i ⊓ (x.func i) ∈ᴮ y := rfl

@[simp, cleanup] lemma binary_inter_type {x y : bSet 𝔹} : (x ∩ᴮ y).type = x.type := rfl

@[simp, cleanup] lemma binary_inter_func {x y : bSet 𝔹} {i} : (x ∩ᴮ y).func i = x.func i := rfl

lemma mem_binary_inter_iff {x y z : bSet 𝔹} {Γ} : Γ ≤ z ∈ᴮ (x ∩ᴮ y) ↔ (Γ ≤ z ∈ᴮ x ∧ Γ ≤ z ∈ᴮ y) :=
begin
  refine ⟨_,_⟩; intro H,
    { rw[mem_unfold] at H, refine ⟨_,_⟩,
        {bv_cases_at H i H_i, rw[mem_unfold], apply bv_use i,
        refine le_inf _ _,
          { exact bv_and.left (bv_and.left ‹_›) },
          { exact bv_and.right ‹_› }},
        { simp only with cleanup at *, bv_cases_at H i H_i, rw[mem_unfold],
          bv_split, bv_split, rw[mem_unfold] at H_i_left_right,
          bv_cases_at H_i_left_right j H_j, apply bv_use j,
          bv_split, from le_inf ‹_› (by bv_cc) } },

    { rcases H with ⟨H₁,H₂⟩, rw mem_unfold at H₁ ⊢,
      bv_cases_at H₁ i H_i, apply bv_use i, rw[binary_inter_bval],
      bv_split, bv_split_goal, bv_cc },
end

lemma subset_binary_inter_iff {x y z : bSet 𝔹} {Γ} : Γ ≤ z ⊆ᴮ x ∩ᴮ y ↔ (Γ ≤ z ⊆ᴮ x ∧ Γ ≤ z ⊆ᴮ y) :=
begin
  refine ⟨_,_⟩; intro H,
    { refine ⟨_,_⟩,
      { rw subset_unfold' at H ⊢, bv_intro w, bv_imp_intro Hw,
        exact (mem_binary_inter_iff.mp (H w ‹_›)).left },
      { rw subset_unfold' at H ⊢, bv_intro w, bv_imp_intro Hw,
        exact (mem_binary_inter_iff.mp (H w ‹_›)).right }},
    { cases H with H₁ H₂, rw subset_unfold', bv_intro w, bv_imp_intro Hw, rw mem_binary_inter_iff,
      refine ⟨_,_⟩,
        { exact mem_of_mem_subset H₁ ‹_› },
        { exact mem_of_mem_subset H₂ ‹_› }}
end

lemma binary_inter_symm {x y : bSet 𝔹} {Γ} : Γ ≤ x ∩ᴮ y =ᴮ y ∩ᴮ x :=
begin
  apply mem_ext;
    {bv_intro z, bv_imp_intro H_mem, simp[mem_binary_inter_iff] at H_mem ⊢, simp*}
end

lemma B_congr_binary_inter_left {y : bSet 𝔹} : B_congr (λ x, x ∩ᴮ y) :=
begin
  intros x₁ x₂ Γ H_eq, dsimp, apply mem_ext;
    {bv_intro z, bv_imp_intro H_mem, simp[mem_binary_inter_iff] at *,
    cases H_mem, exact ⟨by bv_cc, ‹_›⟩ }
end

lemma B_congr_binary_inter_right {y : bSet 𝔹} : B_congr (λ x, y ∩ᴮ x) :=
begin
  intros x₁ x₂ Γ H_eq, dsimp, apply mem_ext;
    {bv_intro z, bv_imp_intro H_mem, simp[mem_binary_inter_iff] at *,
    cases H_mem, exact ⟨‹_›, by bv_cc⟩ }
end

lemma binary_inter_subset_left {x y : bSet 𝔹} {Γ} : Γ ≤ x ∩ᴮ y ⊆ᴮ x :=
by { rw[subset_unfold'], bv_intro z, bv_imp_intro Hz,
       from (mem_binary_inter_iff.mp Hz).left }

lemma binary_inter_subset_right {x y : bSet 𝔹} {Γ} : Γ ≤ x ∩ᴮ y ⊆ᴮ y :=
begin -- TODO(jesse): why isn't the motive being computed correctly here?
  suffices this : ∀ z (H : Γ ≤ y ∩ᴮ x ⊆ᴮ z), Γ ≤ x ∩ᴮ y ⊆ᴮ z,
    from this _ binary_inter_subset_left,
  exact λ z _,
    @bv_rw' 𝔹 _ (x ∩ᴮ y) (y ∩ᴮ x) _ (binary_inter_symm) (λ w, w ⊆ᴮ z) (by simp) ‹_›
end

lemma unordered_pair_symm (x y : bSet 𝔹) {Γ : 𝔹} : Γ ≤ {x,y} =ᴮ {y,x} :=
begin
  apply mem_ext; unfold has_insert.insert bSet.insert1; bv_intro; bv_imp_intro;
  {simp at *, bv_or_elim_at H, apply le_sup_right_of_le, apply mem_singleton_of_eq,
  from bv_symm H.left, apply le_sup_left_of_le, rw[bv_eq_symm], apply eq_of_mem_singleton,
  from ‹_›}
end

lemma binary_union_symm {x y : bSet 𝔹} {Γ} : Γ ≤ binary_union x y =ᴮ binary_union y x :=
begin
  simp[binary_union], apply mem_ext; bv_intro z; bv_imp_intro,
  have := (bv_union_spec_split {x, y} z).mp ‹_›, rw[bv_union_spec_split],
  bv_cases_at this w, bv_split_at this_1, apply bv_use w,
  refine le_inf _ ‹_›, apply bv_rw' (unordered_pair_symm _ _), simp, from ‹_›,
  have := unordered_pair_symm x y, show 𝔹, from Γ_1,
  let a := _, let b := _, change Γ_1 ≤ a =ᴮ b at this, change Γ_1 ≤ z ∈ᴮ bv_union a,
  suffices : Γ_1 ≤ bv_union a =ᴮ bv_union b,
    by {apply bv_rw' this, simpa},
  exact B_congr_bv_union ‹_›
end

/-- The successor operation on sets (in particular von Neumman ordinals) -/
@[reducible]def succ (x : bSet 𝔹) := bSet.insert1 x x

lemma succ_eq_binary_union {x : bSet 𝔹} {Γ} : Γ ≤ succ x =ᴮ binary_union {x} x :=
begin
  simp[succ, binary_union], apply mem_ext,
  {bv_intro z, simp, bv_imp_intro, bv_or_elim_at H, apply bv_rw' H.left, simp,
   apply (bv_union_spec_split _ x).mpr, apply bv_use ({x} : bSet 𝔹),
   refine le_inf _ (le_trans (le_top) mem_singleton), change _ ≤ _ ∈ᴮ insert _ _,
   simp, apply le_sup_right_of_le, from le_trans (le_top) mem_singleton,
   apply (bv_union_spec_split _ z).mpr, apply bv_use x, refine le_inf _ ‹_›,
   change _ ≤ _ ∈ᴮ insert _ _, simp},
  {bv_intro z, simp, bv_imp_intro, rw[bv_union_spec_split] at H, bv_cases_at H y,
   bv_split, change Γ_2 ≤ _ ∈ᴮ insert _ _ at H_1_left,
   simp at H_1_left, bv_or_elim_at H_1_left, apply le_sup_right_of_le,
   apply bv_rw' (bv_symm ‹_›), simp, from ‹_›,
   apply le_sup_left_of_le,
   have : Γ_3 ≤ {x} =ᴮ y, apply eq_of_mem_singleton, from ‹_›,
   suffices : Γ_3 ≤ z ∈ᴮ {x}, rw[bv_eq_symm], apply eq_of_mem_singleton,
   from ‹_›, apply bv_rw' this, simp, from ‹_›}
end

lemma succ_eq_binary_union' {x : bSet 𝔹} {Γ} : Γ ≤ succ x =ᴮ binary_union x {x} :=
by {apply bv_rw' (@binary_union_symm 𝔹 _ x {x} Γ), simp, from succ_eq_binary_union}

@[reducible]def pair (x y : bSet 𝔹) : bSet 𝔹 := {{x}, {x,y}}

-- lemma pair_type (x y : bSet 𝔹) : (pair x y).type = begin end := sorry

--TODO(jesse) write a tactic to automate this type of argument
@[simp]lemma subst_congr_pair_left {x z y : bSet 𝔹} : x =ᴮ z ≤ pair x y =ᴮ pair z y :=
begin
  unfold pair, have this₁ : x =ᴮ z ≤ {{x},{x,y}} =ᴮ {{z},{x,y}} := by simp*,
  have this₂ : x =ᴮ z ≤ {{z},{x,y}} =ᴮ {{z},{z,y}} := by simp*,
  apply bv_trans; from ‹_›
end

@[simp]lemma subst_congr_pair_left' {x z y : bSet 𝔹} {Γ : 𝔹} :
  Γ ≤ x=ᴮ z → Γ ≤ pair x y =ᴮ pair z y := poset_yoneda_inv Γ (subst_congr_pair_left)

lemma subst_congr_pair_right {x y z : bSet 𝔹} : y =ᴮ z ≤ pair x y =ᴮ pair x z :=
by unfold pair; simp*

lemma subst_congr_pair_right' {Γ} {x y z : bSet 𝔹} (H : Γ ≤ y =ᴮ z) : Γ ≤ pair x y =ᴮ pair x z :=
poset_yoneda_inv Γ (subst_congr_pair_right) ‹_›

lemma pair_congr {x₁ x₂ y₁ y₂ : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ x₁ =ᴮ y₁) (H₂ : Γ ≤ x₂ =ᴮ y₂) : Γ ≤ pair x₁ x₂ =ᴮ pair y₁ y₂ :=
begin
  apply bv_rw' H₁,
    {intros v₁ v₂, tidy_context,
      have : Γ_1 ≤ pair v₂ x₂ =ᴮ pair v₁ x₂,
        by {apply subst_congr_pair_left', rwa[bv_eq_symm]},
      from bv_trans this a_right,},
  apply bv_rw' H₂,
    {intros v₁ v₂, tidy_context,
       have : Γ_1 ≤ pair y₁ v₂ =ᴮ pair y₁ v₁,
         by {apply subst_congr_pair_right', rwa[bv_eq_symm]},
       from bv_trans this a_right},
  from bv_refl
end

@[simp]lemma B_congr_insert1_left {y : bSet 𝔹} : B_congr (λ x, bSet.insert1 x y) :=
λ _ _ _, poset_yoneda_inv _ subst_congr_insert1_left

@[simp]lemma B_congr_insert1_right {y : bSet 𝔹} : B_congr (λ x, bSet.insert1 y x) :=
λ _ _ _, poset_yoneda_inv _ subst_congr_insert1_right

@[simp]lemma B_congr_succ : B_congr (succ : bSet 𝔹 → bSet 𝔹) :=
λ x y,
  begin
    unfold succ, intros,
    have : Γ ≤ bSet.insert1 x x =ᴮ bSet.insert1 x y,
      by {simp*},
    have : Γ ≤ bSet.insert1 x y =ᴮ bSet.insert1 y y,
      by {simp*},
    bv_cc
  end

@[simp]lemma B_congr_pair_left {y : bSet 𝔹} : B_congr (λ x, pair x y) :=
λ _ _ _, poset_yoneda_inv _ subst_congr_pair_left

@[simp]lemma B_congr_pair_right {y : bSet 𝔹} : B_congr (λ x, pair y x) :=
λ _ _ _, poset_yoneda_inv _ subst_congr_pair_right

@[simp]lemma B_ext_pair_left {ϕ : bSet 𝔹 → 𝔹} {H : B_ext ϕ} {x} : B_ext (λ z, ϕ ((λ w, pair w x) z)) :=
by simp[H]

@[simp]lemma B_ext_pair_right {ϕ : bSet 𝔹 → 𝔹} {H : B_ext ϕ} {x} : B_ext (λ z, ϕ ((λ w, pair x w) z)) := by simp[H]

example {y z : bSet 𝔹} : ⊤ ≤ ({y,z} : bSet 𝔹) =ᴮ ({z,y}) := insert1_symm _ _

@[simp]lemma B_ext_pair_mem_left {x y : bSet 𝔹} : B_ext (λ z, pair z x ∈ᴮ y) :=
B_ext_term (λ w, w ∈ᴮ y) (λ z, pair z x)

@[simp]lemma B_ext_pair_mem_right {x y : bSet 𝔹} : B_ext (λ z, pair x z ∈ᴮ y) :=
B_ext_term (λ w, w ∈ᴮ y) (λ z, pair x z)

lemma eq_of_eq_pair'_left {x z y : bSet 𝔹} : pair x y =ᴮ pair z y ≤ x =ᴮ z :=
begin
  unfold pair, unfold has_insert.insert, rw[bv_eq_unfold], fapply bv_specialize_left,
  exact some none, fapply bv_specialize_right, exact some none, simp,
  rw[inf_sup_right_left_eq], repeat{apply bv_or_elim},
  {apply le_trans, apply inf_le_inf; apply eq_inserted_of_eq_singleton, {[smt] eblast_using[bv_eq_symm, bv_eq_trans]}},
  {apply inf_le_right_of_le, apply le_trans, apply eq_of_mem_singleton', apply eq_of_eq_singleton, refl},
  {apply inf_le_left_of_le, apply le_trans, apply eq_of_mem_singleton', apply eq_of_eq_singleton, rw[bv_eq_symm]},
  {apply inf_le_left_of_le, apply le_trans, apply eq_of_mem_singleton', apply eq_of_eq_singleton, rw[bv_eq_symm]}
end

lemma inserted_eq_of_insert_eq {y v w : bSet 𝔹} : {v,y} =ᴮ {v,w} ≤ y =ᴮ w :=
begin
  unfold has_insert.insert, rw[bv_eq_unfold], apply bv_specialize_left none,
  apply bv_specialize_right none, change (⊤ ⟹ _) ⊓ (⊤ ⟹ _ : 𝔹) ≤ _, simp,
  rw[inf_sup_right_left_eq], repeat{apply bv_or_elim},
  apply inf_le_left, apply inf_le_left, apply inf_le_right_of_le, rw[bv_eq_symm],
  apply le_trans, apply inf_le_inf; apply eq_of_mem_singleton',
  {[smt] eblast_using[bv_eq_symm, bv_eq_trans]}
end

lemma eq_of_eq_pair'_right {x z y : bSet 𝔹} : pair y x =ᴮ pair y z ≤ x =ᴮ z :=
begin
  unfold pair has_insert.insert, rw[bv_eq_unfold], apply bv_specialize_left none,
  apply bv_specialize_right none, unfold singleton, simp, rw[inf_sup_right_left_eq],
  repeat{apply bv_or_elim},
    {apply inf_le_left_of_le, apply inserted_eq_of_insert_eq},
    {apply inf_le_left_of_le, apply inserted_eq_of_insert_eq},
    {apply inf_le_right_of_le, rw[bv_eq_symm], apply inserted_eq_of_insert_eq},
    {apply le_trans, apply inf_le_inf; apply eq_of_mem_singleton',
     apply le_trans, apply inf_le_inf; apply eq_inserted_of_eq_singleton, rw[bv_eq_symm], apply bv_eq_trans}
end

run_cmd do mk_simp_attr `dnf, mk_simp_attr `cnf

attribute [dnf] inf_sup_left inf_sup_right

attribute [cnf] sup_inf_left sup_inf_right

/- Taken together, eq_of_eq_pair_left and eq_of_eq_pair_right say that x = v and y = w if and only if pair x y = pair v w -/
theorem eq_of_eq_pair_left {x y v w: bSet 𝔹} : pair x y =ᴮ pair v w ≤ x =ᴮ v :=
begin
  unfold pair has_insert.insert, rw[bv_eq_unfold], apply bv_specialize_left none, apply bv_specialize_right (some none),
  unfold singleton, simp, simp only with dnf, repeat{apply bv_or_elim},
  {apply inf_le_right_of_le, apply le_trans, apply eq_inserted_of_eq_singleton', rw[bv_eq_symm]},
  {apply inf_le_left_of_le, rw[mem_unfold], apply bv_Or_elim, intro i, cases i,
   apply inf_le_right_of_le, simp, rw[bv_eq_symm], apply le_trans, apply eq_inserted_of_eq_singleton', rw[bv_eq_symm],
   repeat{cases i}},
  {apply inf_le_right_of_le, apply le_trans, fapply eq_of_mem_singleton, from {x}, from {v},
   refl, apply eq_of_eq_singleton, refl},
  {apply inf_le_right_of_le, apply le_trans, fapply eq_of_mem_singleton, from {x}, from {v},
   refl, apply eq_of_eq_singleton, refl}
end

lemma eq_of_eq_pair_left' {x y v w : bSet 𝔹} {Γ} : Γ ≤ pair x y =ᴮ pair v w → Γ ≤ x =ᴮ v :=
poset_yoneda_inv Γ eq_of_eq_pair_left

theorem eq_of_eq_pair_right {x y v w: bSet 𝔹} : pair x y =ᴮ pair v w ≤ y =ᴮ w :=
begin
  apply bv_have, apply eq_of_eq_pair_left,
  apply le_trans, show 𝔹, from pair v y =ᴮ pair v w,
  rw[inf_comm], apply le_trans, apply inf_le_inf, swap, refl,
  apply subst_congr_pair_left, exact y, rw[bv_eq_symm],
  apply bv_eq_trans, apply eq_of_eq_pair'_right
end

lemma eq_of_eq_pair_right' {x y v w : bSet 𝔹} {Γ} : Γ ≤ pair x y =ᴮ pair v w → Γ ≤ y =ᴮ w :=
poset_yoneda_inv Γ eq_of_eq_pair_right

lemma eq_of_eq_pair {x y z w : bSet 𝔹} {Γ : 𝔹} (H_eq : Γ ≤ pair x y =ᴮ pair z w) :
  Γ ≤ x =ᴮ z ∧ Γ ≤ y =ᴮ w :=
⟨eq_of_eq_pair_left' ‹_›, eq_of_eq_pair_right' ‹_›⟩

lemma pair_eq_pair_iff {x y x' y' : bSet 𝔹} {Γ : 𝔹}
  : Γ ≤ pair x y =ᴮ pair x' y' ↔ Γ ≤ x =ᴮ x' ∧ Γ ≤ y =ᴮ y' :=
iff.intro (λ _, eq_of_eq_pair ‹_›) (λ ⟨_,_⟩, pair_congr ‹_› ‹_›)

@[reducible]def prod (v w : bSet 𝔹) : bSet 𝔹 := ⟨v.type × w.type, λ a, pair (v.func a.1) (w.func a.2), λ a, (v.bval a.1) ⊓ (w.bval a.2)⟩

@[simp, cleanup]lemma prod_type {v w : bSet 𝔹} : (prod v w).type = (v.type × w.type) := by refl

@[simp, cleanup]lemma prod_func {v w : bSet 𝔹} {pr} : (prod v w).func pr = pair (v.func (pr.1))
 (w.func (pr.2)) := by refl

@[simp, cleanup]lemma prod_bval {v w : bSet 𝔹} {a b} : (prod v w).bval (a,b) = v.bval a ⊓ w.bval b := by refl

@[simp, cleanup]lemma prod_type_forall {v w : bSet 𝔹} {ϕ : (prod v w).type → 𝔹} :
  (⨅(z:(prod v w).type), ϕ z) = ⨅(z : v.type × w.type), ϕ z :=
by refl

@[simp]lemma prod_check_bval {x y : pSet.{u}} {pr} : (prod x̌ y̌ : bSet 𝔹).bval pr = ⊤ :=
begin
  dsimp only with cleanup, simp
end

lemma prod_mem_old {v w x y : bSet 𝔹} : x ∈ᴮ v ⊓ y ∈ᴮ w ≤ pair x y ∈ᴮ prod v w :=
begin
  simp[pair, prod], simp only[mem_unfold], apply bv_cases_left, intro i,
  apply bv_cases_right, intro j, apply bv_use (i,j), tidy,
    {rw[inf_assoc], apply inf_le_left},
    {rw[inf_comm], simp [inf_assoc]},
    {let a := _, let b := _, change (bval v i ⊓ a) ⊓ (bval w j ⊓ b) ≤ _,
     have : a ⊓ b ≤ {{x}, {x, y}} =ᴮ {{func v i}, {x,y}}, by simp*,
     have : a ⊓ b ≤ {{func v i}, {x,y}} =ᴮ {{func v i}, {func v i, func w j}},
       by {apply subst_congr_insert1_left'', have this₁ : a ⊓ b ≤ {x,y} =ᴮ {func v i, y}, by simp*,
       have this₂ : a ⊓ b ≤ {func v i, y} =ᴮ {func v i, func w j}, by simp*,
       from bv_trans ‹_› ‹_›},

     apply le_trans, show 𝔹, from a ⊓ b,
       by {ac_change' (bval v i ⊓ bval w j) ⊓ (a ⊓ b) ≤ a ⊓ b, from inf_le_right},
     from bv_trans ‹_› ‹_›}
end

lemma prod_mem {v w x y : bSet 𝔹} {Γ} : Γ ≤ x ∈ᴮ v → Γ ≤ y ∈ᴮ w → Γ ≤ pair x y ∈ᴮ prod v w :=
λ H₁ H₂, by {transitivity x ∈ᴮ v ⊓ y ∈ᴮ w, bv_split_goal, from prod_mem_old}

lemma mem_left_of_prod_mem {v w x y : bSet 𝔹} {Γ : 𝔹} : Γ ≤ pair x y ∈ᴮ prod v w → Γ ≤ x ∈ᴮ v :=
begin
  intro H_pair_mem, rw[mem_unfold] at H_pair_mem, bv_cases_at H_pair_mem p, cases p with i j,
  dsimp at *, bv_split, rw[mem_unfold], apply bv_use i,
  replace H_pair_mem_1_right := eq_of_eq_pair_left' H_pair_mem_1_right,
  simp only [le_inf_iff] at *, simp*
end

lemma mem_right_of_prod_mem {v w x y : bSet 𝔹} {Γ : 𝔹} : Γ ≤ pair x y ∈ᴮ prod v w → Γ ≤ y ∈ᴮ w :=
begin
  intro H_pair_mem, rw[mem_unfold] at H_pair_mem, bv_cases_at H_pair_mem p, cases p with i j,
  dsimp at *, bv_split, rw[mem_unfold], apply bv_use j,
  replace H_pair_mem_1_right := eq_of_eq_pair_right' H_pair_mem_1_right,
  simp only [le_inf_iff] at *, simp*
end

@[simp]lemma mem_prod_iff {v w x y : bSet 𝔹} {Γ} : Γ ≤ pair x y ∈ᴮ prod v w ↔ (Γ ≤ x ∈ᴮ v ∧ Γ ≤ y ∈ᴮ w) :=
⟨λ _, ⟨mem_left_of_prod_mem ‹_›, mem_right_of_prod_mem ‹_›⟩, λ ⟨_,_⟩, prod_mem ‹_› ‹_›⟩

@[simp]lemma mem_prod {v w x y : bSet 𝔹} {Γ} (H_mem₁ : Γ ≤ x ∈ᴮ v) (H_mem₂ : Γ ≤ y ∈ᴮ w) :
 Γ ≤ pair x y ∈ᴮ prod v w :=
mem_prod_iff.mpr (by simp*)

@[simp]lemma B_congr_prod_left {y : bSet 𝔹} : B_congr (λ x, prod x y) :=
begin
  intros a b Γ H_eq,
  dsimp, rw bv_eq_unfold,
  refine le_inf _ _,
    { bv_intro pr, bv_imp_intro Hpr, erw mem_prod_iff, refine ⟨_,_⟩,
      { apply bv_rw' (bv_symm H_eq), simp, simp at Hpr, from mem.mk'' (Hpr.left) },
      { simp at Hpr, from mem.mk'' (Hpr.right) }},
    { bv_intro pr, bv_imp_intro Hpr, erw mem_prod_iff, refine ⟨_,_⟩,
      { apply bv_rw' (H_eq), simp, simp at Hpr, from mem.mk'' (Hpr.left) },
      { simp at Hpr, from mem.mk'' (Hpr.right) } }
end

@[simp]lemma B_congr_prod_right {x : bSet 𝔹} : B_congr (λ y, prod x y) :=
begin
  intros a b Γ H_eq,
  dsimp, rw bv_eq_unfold,
  refine le_inf _ _,
    { bv_intro pr, bv_imp_intro Hpr, erw mem_prod_iff, refine ⟨_,_⟩,
      { apply bv_rw' (bv_symm H_eq), simp, simp at Hpr, from mem.mk'' (Hpr.left) },
      { simp at Hpr, apply bv_rw' (bv_symm H_eq), simp, exact mem.mk'' Hpr.right }},
    { bv_intro pr, bv_imp_intro Hpr, erw mem_prod_iff, refine ⟨_,_⟩,
      { apply bv_rw' (H_eq), simp, simp at Hpr, from mem.mk'' (Hpr.left) },
      { simp at Hpr, apply bv_rw' (H_eq), simp, exact mem.mk'' Hpr.right } }
end

lemma prod_congr {x₁ x₂ y₁ y₂ : bSet 𝔹} {Γ} (H₁ : Γ ≤ x₁ =ᴮ x₂) (H₂ : Γ ≤ y₁ =ᴮ y₂) : Γ ≤ prod x₁ y₁ =ᴮ prod x₂ y₂ :=
begin
  have := B_congr_prod_left H₁, show bSet 𝔹, from y₁,
  dsimp at this, refine bv_trans this _,
  from B_congr_prod_right H₂
end

lemma mem_prod_iff₂ {x y z : bSet 𝔹} {Γ} : Γ ≤ z ∈ᴮ prod x y ↔ ∃ (v) (Hv : Γ ≤ v ∈ᴮ x) (w) (Hw : Γ ≤ w ∈ᴮ y), Γ ≤ z =ᴮ pair v w :=
begin
  refine ⟨_,_⟩; intro H, swap,
    { rcases H with ⟨v,Hv,w,Hw,H_eq⟩, apply bv_rw' H_eq, simp, rw mem_prod_iff, simp* },
    { suffices : Γ ≤ ⨆ v, v ∈ᴮ x ⊓ ⨆ w, w ∈ᴮ y ⊓ z =ᴮ pair v w,
        by {rcases (exists_convert this) with ⟨v, H'v⟩,
            use v, bv_split_at H'v, use ‹_›,
            rcases (exists_convert H'v_right) with ⟨w, H'w⟩,
            use w, bv_split_at H'w, from ⟨‹_›,‹_›⟩},
      rw mem_unfold at H, bv_cases_at H pr Hpr, bv_split_at Hpr,
      apply bv_use (x.func pr.1), simp at Hpr_left, cases Hpr_left, refine le_inf _ _,
        { from mem.mk'' ‹_› },
        { apply bv_use (y.func pr.2), refine le_inf _ _,
          { from mem.mk'' ‹_› },
          { from Hpr_right } } }
end

lemma prod_ext {S₁ S₂ x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ S₁ ⊆ᴮ prod x y) (H₂ : Γ ≤ S₂ ⊆ᴮ prod x y) (H_prod_ext : Γ ≤ ⨅ v, v ∈ᴮ x ⟹ ⨅ w, w∈ᴮ y ⟹ (pair v w ∈ᴮ S₁ ⇔ pair v w ∈ᴮ S₂)) : Γ ≤ S₁ =ᴮ S₂ :=
begin
  apply mem_ext,
    {bv_intro z, bv_imp_intro Hz_mem,
    have Hz_mem' : Γ_1 ≤ z ∈ᴮ prod x y := mem_of_mem_subset ‹_› ‹_›,
    rw mem_prod_iff₂ at Hz_mem', rcases Hz_mem' with ⟨v,Hv,w,Hw,H_eq⟩,
    replace H_prod_ext := H_prod_ext v,
    replace H_prod_ext := H_prod_ext ‹_›,
    replace H_prod_ext := H_prod_ext w,
    replace H_prod_ext := H_prod_ext ‹_›,
    bv_split_at H_prod_ext,
    apply bv_rw' H_eq, simp, have := bv_rw'' H_eq Hz_mem, exact H_prod_ext_left ‹_›},
    {bv_intro z, bv_imp_intro Hz_mem,
    have Hz_mem' : Γ_1 ≤ z ∈ᴮ prod x y := mem_of_mem_subset H₂ ‹_›,
    rw mem_prod_iff₂ at Hz_mem', rcases Hz_mem' with ⟨v,Hv,w,Hw,H_eq⟩,
    replace H_prod_ext := H_prod_ext v,
    replace H_prod_ext := H_prod_ext ‹_›,
    replace H_prod_ext := H_prod_ext w,
    replace H_prod_ext := H_prod_ext ‹_›,
    bv_split_at H_prod_ext,
    apply bv_rw' H_eq, simp, have := bv_rw'' H_eq Hz_mem, exact H_prod_ext_right ‹_›}
end


@[simp]lemma check_singleton {x : pSet.{u}} {Γ : 𝔹} : Γ ≤ {x}̌  =ᴮ {x̌} :=
begin
  unfold singleton, unfold has_insert.insert, simp
end

@[simp]lemma check_unordered_pair {x y : pSet.{u}} {Γ} : Γ ≤ ({x,y})̌ =ᴮ ({x̌, y̌} : bSet 𝔹) :=
begin
  unfold has_insert.insert, simp
end

-- TODO add B_congr lemmas for insert1
@[simp]lemma eq_unordered_pair_of_eq {a b c d : bSet 𝔹} {Γ} (H₁ : Γ ≤ a =ᴮ c) (H₂ : Γ ≤ b =ᴮ d)
  : Γ ≤ {a,b} =ᴮ {c,d} :=
begin
  have : _ ≤ {_, b} =ᴮ {_,b} := @subst_congr_insert1_right'' _ _ _ _ _ _ H₁,
  refine bv_trans this _, apply subst_congr_insert1_left', from ‹_›
end

lemma check_pair {x y : pSet.{u}} {Γ} : Γ ≤ (pSet.pair x y)̌  =ᴮ bSet.pair (x̌) (y̌ : bSet 𝔹) :=
begin
  unfold pSet.pair, unfold bSet.pair,
  have : Γ ≤ {{x}, {x, y}}̌  =ᴮ {{x}̌ , {x,y}̌ } := check_unordered_pair,
  refine bv_trans this _,
  refine eq_unordered_pair_of_eq _ _, simp, simp
end

lemma check_prod {x y : pSet.{u}} {Γ : 𝔹} : Γ ≤ (pSet.prod x y)̌  =ᴮ bSet.prod x̌ y̌ :=
begin
  rw bv_eq_unfold, refine le_inf _ _; bv_intro pr; bv_imp_intro Hbvpr,
    { cases pr with i j, rw mem_unfold, apply bv_use (check_cast.symm i, check_cast.symm j),
      refine le_inf (by simp) _, change Γ_1 ≤ (pSet.pair (x.func i) (y.func j))̌  =ᴮ pair _ _,
      refine bv_trans check_pair _, rw pair_eq_pair_iff,
      refine ⟨_,_⟩,
        { cases x, from bv_refl },
        { cases y, from bv_refl }},
    { cases pr with i j, change _ ≤ pair _ _ ∈ᴮ _,
      dsimp only, rw check_func, rw check_func,
      change _ ≤ (λ w, w ∈ᴮ (pSet.prod x y)̌ ) _, apply bv_rw' (bv_symm check_pair), simp,
      apply check_mem, simp [pSet.mem_prod_iff] }
end

-- /-- f is =ᴮ-extensional on x if for every w₁ and w₂ ∈ x, if w₁ =ᴮ w₂, then for every v₁ and v₂, if (w₁,v₁) ∈ f and (w₂,v₂) ∈ f, then v₁ =ᴮ v₂ -/
-- @[reducible]def is_extensional (x f : bSet 𝔹) : 𝔹 :=
-- ⨅w₁, w₁ ∈ᴮ x ⟹ (⨅w₂, w₂ ∈ᴮ x ⟹ (w₁ =ᴮ w₂ ⟹ ⨅v₁ v₂, (pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f) ⟹ v₁ =ᴮ v₂))

/-- f is =ᴮ-extensional if for every w₁ w₂ v₁ v₂, if pair (w₁ v₁) and pair (w₂ v₂) ∈ f and
    w₁ =ᴮ w₂, then v₁ =ᴮ v₂ -/
@[reducible]def is_func (f : bSet 𝔹) : 𝔹 :=
  ⨅ w₁, ⨅w₂, ⨅v₁, ⨅ v₂, pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⟹ (w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂)

-- TODO(jesse): automate this argument with simp lemmas
-- for restricting universally quantifier statements to subsets
@[simp] lemma is_func_subset_of_is_func {f g : bSet 𝔹} {Γ} (H : Γ ≤ is_func f) (H_sub : Γ ≤ g ⊆ᴮ f) : Γ ≤ is_func g :=
begin
  bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂, bv_imp_intro H',
  replace H := H w₁ w₂ v₁ v₂,
  suffices this : Γ_1 ≤ pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f,
    by {exact H ‹_›},
  bv_split, refine le_inf _ _; rw[subset_unfold'] at H_sub,
  exact H_sub (pair w₁ v₁) ‹_›, exact H_sub (pair w₂ v₂) ‹_›
end

-- lemma check_is_func {g : pSet} (H_ext : pSet.is_extensional g) {Γ : 𝔹} : Γ ≤ is_func (ǧ) :=
-- begin
--   unfold pSet.is_extensional at H_ext, unfold is_func,
--   bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂,
--   bv_imp_intro H, bv_split, bv_imp_intro H_eq,
--   sorry
-- end


/-- f is a functional relation if for every z ∈ x, if there exists a w ∈ y such that (z,w) ∈ f, then for every w' ∈ y such that (z,w') ∈ f, w' =ᴮ w -/
-- @[reducible] def is_functional (x y f : bSet 𝔹) : 𝔹 :=
-- ⨅z, (z∈ᴮ x ⟹ (⨆w, w ∈ᴮ y ⊓ pair z w ∈ᴮ f ⊓ (⨅w', w' ∈ᴮ y ⟹ (pair z w' ∈ᴮ f ⟹ w =ᴮ w'))))

@[reducible]def is_functional (f : bSet 𝔹) : 𝔹 :=
⨅z, (⨆w, pair z w ∈ᴮ f) ⟹ (⨆w', ⨅w'', pair z w'' ∈ᴮ f ⟹ w' =ᴮ w'')

lemma is_functional_of_is_func (f : bSet 𝔹) {Γ} (H : Γ ≤ is_func f) : Γ ≤ is_functional f :=
begin
  unfold is_functional, unfold is_func at H,
  bv_intro z, bv_imp_intro w_spec,
  bv_cases_at w_spec w, clear w_spec,
  replace H := H z z, apply bv_use w,
  bv_intro w', bv_imp_intro Hw',
  from H w w' (le_inf ‹_› ‹_›) (bv_refl)
end

@[reducible]def is_total (x y f : bSet 𝔹) : 𝔹 :=
(⨅w₁, w₁ ∈ᴮ x ⟹ ⨆w₂, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f)

-- bounded version of is_total
@[reducible]def is_total' (x y f : bSet 𝔹) : 𝔹 :=
(⨅ i, x.bval i ⟹ ⨆j, y.bval j ⊓ pair (x.func i) (y.func j) ∈ᴮ f)

lemma is_total_iff_is_total' {Γ : 𝔹} {x y f} : Γ ≤ is_total x y f ↔ Γ ≤ is_total' x y f :=
begin
  unfold is_total, rw ←bounded_forall,
  swap, {change B_ext _, apply B_ext_supr,
  intro i, apply B_ext_inf, simp, from B_ext_pair_mem_left},
  refine ⟨_,_⟩; intro H,
    { bv_intro i, bv_imp_intro Hi, replace H := H i Hi,
      rw ←bounded_exists at H, swap, {change B_ext _, from B_ext_pair_mem_right }, from ‹_› },
    { bv_intro i, bv_imp_intro Hi, replace H := H i Hi,
       rw ←bounded_exists, swap, { change B_ext _, from B_ext_pair_mem_right }, from ‹_› }
end


@[simp]lemma is_total_subset_of_is_total {S x y f : bSet 𝔹} {Γ} (H_is_total : Γ ≤ is_total x y f) (H_subset : Γ ≤ S ⊆ᴮ x) : Γ ≤ is_total S y f :=
by {simp*, intro z, bv_imp_intro Hz, from H_is_total z (mem_of_mem_subset ‹_› ‹_›)}

/-- f is (more precisely, contains) a function from x to y if for every element of x, there exists an element of y such that the pair is in f, and f is a function -/
@[reducible]def is_func' (x y f : bSet 𝔹) : 𝔹 :=
  is_func f ⊓ is_total x y f

@[simp]lemma is_func_of_is_func' {x y f : bSet 𝔹} {Γ} (H : Γ ≤ is_func' x y f) : Γ ≤ is_func f :=
bv_and.left ‹_›

lemma is_total_of_is_func' {x y f : bSet 𝔹} {Γ : 𝔹} (H_is_func' : Γ ≤ is_func' x y f)
  : Γ ≤ is_total x y f :=
bv_and.right ‹_›

lemma is_func'_empty {Γ : 𝔹} {x} : Γ ≤ is_func' (∅ : bSet 𝔹) x ∅ :=
begin
  refine le_inf _ _,
  bv_intro x, bv_intro y, bv_intro z, bv_intro w,
  bv_imp_intro H, bv_exfalso,
  exact bot_of_mem_empty (bv_and.left H),
  apply forall_empty
end

-- aka function extensionality
@[simp]lemma eq_of_is_func_of_eq {x y f x' y' : bSet 𝔹} {Γ : 𝔹} (H_is_func : Γ ≤ is_func f)  (H_eq₁ : Γ ≤ x =ᴮ y)
  (H_mem₁ : Γ ≤ pair x x' ∈ᴮ f) (H_mem₂ : Γ ≤ pair y y' ∈ᴮ f) : Γ ≤ x' =ᴮ y' :=
H_is_func x y x' y' (le_inf ‹_› ‹_›) ‹_›

-- aka function extensionality
@[simp]lemma eq_of_is_func'_of_eq {a b x y f x' y' : bSet 𝔹} {Γ : 𝔹} (H_is_func' : Γ ≤ is_func' a b f)  (H_eq₁ : Γ ≤ x =ᴮ y)
  (H_mem₁ : Γ ≤ pair x x' ∈ᴮ f) (H_mem₂ : Γ ≤ pair y y' ∈ᴮ f) : Γ ≤ x' =ᴮ y' :=
by {[smt] eblast_using [eq_of_is_func_of_eq, is_func_of_is_func']}

@[simp]lemma is_func'_subset_of_is_func' {S x y f : bSet 𝔹} {Γ : 𝔹}
  (H_is_func : Γ ≤ is_func' x y f) (H_subset : Γ ≤ S ⊆ᴮ x) : Γ ≤ is_func' S y f :=
begin
  refine le_inf _ _,
   {[smt] eblast_using is_func_of_is_func'},
   from is_total_subset_of_is_total (is_total_of_is_func' ‹_›) ‹_›
end

-- bounded image
def image (x y f : bSet 𝔹) : bSet 𝔹 := subset.mk (λ j : y.type, ⨆ z, z ∈ᴮ x ⊓ pair z (y.func j) ∈ᴮ f)

@[simp]lemma image_subset  {x y f : bSet 𝔹} {Γ} : Γ ≤ (image x y f) ⊆ᴮ y :=
subset.mk_subset

@[simp]lemma mem_image {x y a b f : bSet 𝔹} {Γ} (H_mem : Γ ≤ pair a b ∈ᴮ f) (H_mem'' : Γ ≤ a ∈ᴮ x) (H_mem' : Γ ≤ b ∈ᴮ y) : Γ ≤ b ∈ᴮ image x y f :=
begin
  rw[image, mem_subset.mk_iff],
  rw[mem_unfold] at H_mem', bv_cases_at H_mem' i Hi, apply bv_use i,
  bv_split_at Hi, refine le_inf ‹_› (le_inf _ ‹_›),
  apply bv_use a, refine le_inf ‹_› _,
  apply @bv_rw' _ _ _ _ _ (bv_symm Hi_right) (λ z, pair a z ∈ᴮ f),
  exact B_ext_pair_mem_right, from ‹_›
end

lemma mem_image_iff {x y b f : bSet 𝔹} {Γ} : Γ ≤ b ∈ᴮ image x y f ↔ (Γ ≤ b ∈ᴮ y ) ∧ Γ ≤ ⨆ z, z ∈ᴮ x ⊓ pair z b ∈ᴮ f :=
begin
  refine ⟨_,_⟩; intro H,
    refine ⟨_,_⟩,
    { from mem_of_mem_subset (image_subset) ‹_› },
    { unfold image at H, rw mem_subset.mk_iff at H, bv_cases_at H i Hi, bv_split_at Hi,
      bv_split_at Hi_right, bv_cases_at Hi_right_left z Hz, apply bv_use z, refine le_inf (bv_and.left ‹_›) _,
      change _ ≤ (λ w, w ∈ᴮ f) _, apply bv_rw' Hi_left, simp, from bv_and.right Hz },
    { cases H with _ H, bv_cases_at H z Hz, apply mem_image, from bv_and.right ‹_›, from bv_and.left ‹_›, from ‹_› },
end

@[simp]lemma B_congr_image_left {y f : bSet 𝔹} : B_congr (λ x, image x y f) :=
begin
  intros x y Γ H_eq, refine mem_ext _ _,
    { bv_intro z, bv_imp_intro Hz, rw mem_image_iff at ⊢ Hz,
      rcases Hz with ⟨Hz_mem_y, H⟩, refine ⟨‹_›,_⟩, apply bv_rw' (bv_symm H_eq), simp, repeat { from ‹_› } },
    { bv_intro z, bv_imp_intro Hz, rw mem_image_iff at ⊢ Hz,
      rcases Hz with ⟨Hz_mem_y, H⟩, refine ⟨‹_›,_⟩, apply bv_rw' H_eq, simp, repeat { from ‹_› } }
end

@[simp]lemma B_congr_image_right {x y : bSet 𝔹} : B_congr (λ f, image x y f) :=
begin
  intros x y Γ H_eq, refine mem_ext _ _,
    { bv_intro z, bv_imp_intro Hz, rw mem_image_iff at ⊢ Hz,
      rcases Hz with ⟨Hz_mem_y, H⟩, refine ⟨‹_›,_⟩, apply bv_rw' (bv_symm H_eq), simp, repeat { from ‹_› } },
    { bv_intro z, bv_imp_intro Hz, rw mem_image_iff at ⊢ Hz,
      rcases Hz with ⟨Hz_mem_y, H⟩, refine ⟨‹_›,_⟩, apply bv_rw' H_eq, simp, repeat { from ‹_› } }
end

-- bounded preimage
def preimage (x y f : bSet 𝔹) : bSet 𝔹 := subset.mk (λ i : x.type, ⨆ b, b ∈ᴮ y ⊓
 pair (x.func i) b ∈ᴮ f)

@[simp]lemma preimage_subset {x y f} {Γ : 𝔹} : Γ ≤ (preimage x y f) ⊆ᴮ x := subset.mk_subset

@[simp]lemma mem_preimage {x y a b f : bSet 𝔹} {Γ} (H_mem : Γ ≤ pair a b ∈ᴮ f) (H_mem'' : Γ ≤ a ∈ᴮ x) (H_mem' : Γ ≤ b ∈ᴮ y) : Γ ≤ a ∈ᴮ preimage x y f :=
begin
  rw[preimage, mem_subset.mk_iff],
  rw[mem_unfold] at H_mem'', bv_cases_at H_mem'' i Hi, apply bv_use i,
  bv_split_at Hi, refine le_inf ‹_› (le_inf _ ‹_›),
  apply bv_use b, refine le_inf ‹_› _,
  apply @bv_rw' _ _ _ _ _ (bv_symm Hi_right) (λ z, pair z b ∈ᴮ f),
  exact B_ext_pair_mem_left, from ‹_›
end

/-- f is a function x → y if it is extensional, total, and is a subset of the product of x and y -/
@[reducible]def is_function (x y f : bSet 𝔹) : 𝔹 :=
  is_func' x y f ⊓ (f ⊆ᴮ prod x y)

@[simp]lemma B_ext_is_function_left {y f : bSet 𝔹} : B_ext (λ x, is_function x y f) :=
by simp[is_function]

@[simp]lemma B_ext_is_function_right {x y: bSet 𝔹} : B_ext (λ f, is_function x y f) := by simp

lemma is_func'_of_is_function {Γ : 𝔹} {x y f} (H_func : Γ ≤ is_function x y f) : Γ ≤ is_func' x y f := bv_and.left H_func

lemma eq_of_is_function_of_eq {a b x y f x' y' : bSet 𝔹} {Γ : 𝔹} (H_is_function : Γ ≤ is_function a b f) (H_eq₁ : Γ ≤ x =ᴮ y) (H_mem₁ : Γ ≤ pair x x' ∈ᴮ f) (H_mem₂ : Γ ≤ pair y y' ∈ᴮ f) : Γ ≤ x' =ᴮ y' :=
by {apply eq_of_is_func'_of_eq, from is_func'_of_is_function ‹_›, repeat {assumption}}

lemma subset_prod_of_is_function {Γ : 𝔹} {x y f} (H_func : Γ ≤ is_function x y f) : Γ ≤ f ⊆ᴮ prod x y := bv_and.right H_func

lemma is_total_of_is_function {x y f : bSet 𝔹} {Γ} (H_func : Γ ≤ is_function x y f) : Γ ≤ is_total x y f :=
is_total_of_is_func' (is_func'_of_is_function H_func)

lemma mem_domain_of_is_function {x y f : bSet 𝔹} {Γ} {z w : bSet 𝔹} (H_mem : Γ ≤ pair z w ∈ᴮ f) (H_func : Γ ≤ is_function x y f) : Γ ≤ z ∈ᴮ x :=
begin
  have : Γ ≤ pair z w ∈ᴮ prod x y,
    by { exact mem_of_mem_subset (bv_and.right H_func) ‹_› },
  rw mem_prod_iff at this, from this.left
end

lemma mem_codomain_of_is_function {x y f : bSet 𝔹} {Γ} {z w : bSet 𝔹} (H_mem : Γ ≤ pair z w ∈ᴮ f) (H_func : Γ ≤ is_function x y f) : Γ ≤ w ∈ᴮ y :=
begin
  have : Γ ≤ pair z w ∈ᴮ prod x y,
    by { exact mem_of_mem_subset (bv_and.right H_func) ‹_› },
  rw mem_prod_iff at this, from this.right
end

lemma factor_image_is_func' { x y f : bSet 𝔹 } { Γ } (H_is_func' : Γ ≤ is_func' x y f) : Γ ≤ is_func' x (image x y f) f :=
begin
  refine le_inf (bv_and.left ‹_›) _,
  bv_intro w₁, bv_imp_intro Hw₁,
  have := is_total_of_is_func' H_is_func',
  replace this := this w₁ Hw₁, bv_cases_at this w₂ Hw₂,
  apply bv_use w₂, refine le_inf _ (bv_and.right ‹_›),
  rw mem_image_iff, refine ⟨bv_and.left ‹_›, _⟩,
  apply bv_use w₁, from le_inf ‹_› (bv_and.right ‹_›)
end

lemma factor_image_is_function { x y f : bSet 𝔹 } { Γ } (H_is_function : Γ ≤ is_function x y f) : Γ ≤ is_function x (image x y f) f :=
begin
  refine le_inf _ _,
    { exact factor_image_is_func' (is_func'_of_is_function ‹_›) },
    { rw subset_unfold', bv_intro w, bv_imp_intro Hw,
      have Hw_mem_prod : Γ_1 ≤ w ∈ᴮ prod x y,
        by { apply mem_of_mem_subset (subset_prod_of_is_function ‹_›) ‹_› },
      rw mem_prod_iff₂ at Hw_mem_prod, rcases Hw_mem_prod with ⟨v,Hv,w',Hw', H_eq⟩,
      rw mem_prod_iff₂, use v, use ‹_›, use w',
      refine ⟨_,‹_›⟩,
        { rw mem_image_iff, refine ⟨‹_›, _⟩, apply bv_use v, refine le_inf ‹_› _, bv_cc }}
end

lemma check_is_total {x y f : pSet.{u}} (H_total : pSet.is_total x y f)  {Γ : 𝔹} : Γ ≤ is_total x̌ y̌ f̌ :=
begin
  bv_intro z, bv_imp_intro Hz,
  apply bv_by_contra, bv_imp_intro H,
  classical, by_contra H_nonzero, rw ←bot_lt_iff_not_le_bot at H_nonzero,
  rcases eq_check_of_mem_check ‹_› Hz with ⟨i, Γ', H₁, H₂, H₃⟩,
  simp only with bv_push_neg at H,
  rcases (H_total (x.func i) (by simp)) with ⟨b, Hb_mem, Hb_pair_mem⟩,
  replace H := le_trans H₂ (H (b̌)), suffices this : Γ' ≤ ⊥, by {exact false_of_bot_lt_and_le_bot H₁ ‹_› },
  bv_or_elim_at H,
    { refine bv_absurd _ _ H.left, from check_mem ‹_› },
    { have this : Γ_3 ≤ _ := check_mem Hb_pair_mem,
      refine bv_absurd _ _ H.right,
      apply bv_rw' H₃, from B_ext_pair_mem_left, change _ ≤ (λ w, w ∈ᴮ f̌) _,
      apply bv_rw' (bv_symm check_pair), simp, from ‹_› }
end

lemma check_is_func {x y f : pSet.{u}} (H_func : pSet.is_func x y f) {Γ : 𝔹} : Γ ≤ is_function x̌ y̌ f̌ :=
begin
  refine le_inf (le_inf _ _) _,
    { have : Γ ≤ f̌ ⊆ᴮ _ := check_subset (pSet.subset_prod_of_is_func ‹_›),
      bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂, bv_imp_intro H, bv_split_at H, bv_imp_intro H_eq,
      have H_left' := H_left, have H_right' := H_right,
      replace H_left := mem_of_mem_subset this H_left, replace H_right := mem_of_mem_subset this H_right,
      change _ ≤ (λ w, (pair w₁ v₁) ∈ᴮ w) (pSet.prod x y)̌  at H_left, change _ ≤ (λ w, (pair w₂ v₂) ∈ᴮ w) (pSet.prod x y)̌  at H_right,
      replace H_left :=  bv_rw'' (check_prod) H_left,
      replace H_right :=  bv_rw'' (check_prod) H_right,
      rw mem_prod_iff at H_left H_right,
      rcases H_left with ⟨H₁, H₂⟩, rcases H_right with ⟨H₃, H₄⟩, rw mem_unfold at H₁ H₂ H₃ H₄,
      bv_cases_at H₁ i₁ Hi₁, bv_cases_at H₂ j₁ Hj₁, bv_cases_at H₃ i₂ Hi₂, bv_cases_at H₄ j₂ Hj₂,
      simp at Hi₁ Hj₁ Hi₂ Hj₂, rw check_func at *,
      suffices : Γ_6 ≤ (pSet.func y (check_cast j₁))̌  =ᴮ (pSet.func y (check_cast j₂))̌ ,
        by bv_cc,
      classical, by_cases H_bot : (⊥ < Γ_6), swap,
      {rw le_bot_iff_not_bot_lt at H_bot, from le_trans H_bot bot_le},
      apply check_eq,
      refine pSet.eq_of_is_func_of_eq H_func _ _
               (_ : pSet.equiv (pSet.func x (check_cast i₁)) (pSet.func x (check_cast i₂))),
        { apply check_mem_reflect ‹_›,
          let A := _, change _ ≤ A ∈ᴮ _,
          suffices this : Γ_6 ≤ A =ᴮ pair w₁ v₁,
            by {change _ ≤ (λ w, w ∈ᴮ f̌) _, apply bv_rw' this, simp, from ‹_› },
          refine bv_trans check_pair _, rw pair_eq_pair_iff,
          refine ⟨_,_⟩; apply bv_symm; assumption  },
        { apply check_mem_reflect ‹_›,
          let A := _, change _ ≤ A ∈ᴮ _,
          suffices this : Γ_6 ≤ A =ᴮ pair w₂ v₂,
            by {change _ ≤ (λ w, w ∈ᴮ f̌) _, apply bv_rw' this, simp, from ‹_› },
          refine bv_trans check_pair _, rw pair_eq_pair_iff,
          refine ⟨_,_⟩; apply bv_symm; assumption   },
        { apply check_eq_reflect ‹_›, bv_cc }},
    { from check_is_total (pSet.is_total_of_is_func ‹_›) },
    {  apply bv_rw' (bv_symm check_prod), { simp },
       from check_subset (pSet.subset_prod_of_is_func ‹_›) }
end


def function_of_func' {x y f : bSet 𝔹} {Γ} (H_is_func' : Γ ≤ is_func' x y f) : bSet 𝔹 :=
f ∩ᴮ (prod x y)

lemma function_of_func'_subset {x y f : bSet 𝔹} {Γ} {H_is_func' : Γ ≤ is_func' x y f} :
  Γ ≤ function_of_func' H_is_func' ⊆ᴮ f :=
binary_inter_subset_left

lemma mem_function_of_func'_iff {x y f : bSet 𝔹} {Γ} {H_is_func' : Γ ≤ is_func' x y f} {z} :
Γ ≤ z ∈ᴮ (function_of_func' H_is_func') ↔ Γ ≤ z ∈ᴮ f ∧ Γ ≤ z ∈ᴮ (prod x y) := mem_binary_inter_iff

@[reducible]def is_inj (f : bSet 𝔹) : 𝔹 :=
  ⨅w₁, ⨅ w₂, ⨅v₁, ⨅ v₂, (pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⊓ v₁ =ᴮ v₂) ⟹ w₁ =ᴮ w₂

@[reducible]def is_injective_function (x y f : bSet 𝔹) : 𝔹 := is_function x y f ⊓ is_inj f

lemma is_inj_of_is_injective_function { x y f : bSet 𝔹 } { Γ : 𝔹 } : Γ ≤ is_injective_function x y f → Γ ≤ is_inj f := λ _, bv_and.right ‹_›

lemma factor_image_is_injective_function { x y f : bSet 𝔹 } { Γ : 𝔹 } (H_is_function : Γ ≤ is_injective_function x y f) : Γ ≤ is_injective_function x (image x y f) f :=
begin
  refine le_inf _ _,
    { apply factor_image_is_function, from bv_and.left ‹_› },
    from bv_and.right ‹_›
end

@[simp]lemma B_ext_is_injective_function_left {y f : bSet 𝔹} : B_ext (λ x, is_injective_function x y f) :=
by simp

lemma is_func'_of_is_injective_function {x y f : bSet 𝔹} {Γ}
  (H : Γ ≤ is_injective_function x y f) : Γ ≤ is_func' x y f :=
is_func'_of_is_function $ bv_and.left H

lemma check_is_injective_function {x y f : pSet.{u}} (H_inj : pSet.is_injective_function x y f) {Γ : 𝔹}
  : Γ ≤ bSet.is_injective_function x̌ y̌ f̌ :=
begin
  have : Γ ≤ _ := check_is_func H_inj.left,
  refine le_inf this _, bv_split_at this,
  bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂,
  bv_imp_intro H, bv_split_at H, bv_split_at H_left,
  cases H_inj with _ H_inj,
  unfold pSet.is_inj at H_inj,
  have H₁ := mem_of_mem_subset this_right H_left_left,
  have H₂ := mem_of_mem_subset this_right H_left_right,
  rw [mem_prod_iff] at H₁ H₂,
  cases H₁ with Hw₁ Hv₁, cases H₂ with Hw₂ Hv₂,
  rw mem_unfold at Hw₁ Hv₁ Hw₂ Hv₂,
  bv_cases_at Hw₁ iw₁ Hiw₁,
  bv_cases_at Hw₂ iw₂ Hiw₂,
  bv_cases_at Hv₁ iv₁ Hiv₁,
  bv_cases_at Hv₂ iv₂ Hiv₂,
  rw [check_bval_top, top_inf_eq] at Hiw₁ Hiw₂ Hiv₁ Hiv₂,
  suffices : Γ_5 ≤ (func x̌ iw₁) =ᴮ (func x̌ iw₂),
    by bv_cc,
  simp only [check_func] at ⊢ Hiv₁ Hiv₂ Hiw₁ Hiw₂,
  classical, by_cases H_lt : ⊥ < Γ_5,
  swap, {rw le_bot_iff_not_bot_lt at H_lt, from le_trans H_lt bot_le},
  refine (check_eq $ H_inj _ _ (pSet.func y (check_cast iv₁)) (pSet.func y (check_cast iv₂)) _),
  refine ⟨_,_,_⟩,
    { by_contra, suffices : Γ_5 ≤ ⊥, from false_of_bot_lt_and_le_bot ‹_› ‹_›, apply check_not_mem a,
      suffices : Γ_5 ≤ pair w₁ v₁ =ᴮ (pSet.pair (pSet.func x (check_cast iw₁)) (pSet.func y (check_cast iv₁)))̌ ,
      by {change _ ≤ (λ w, w ∈ᴮ f̌) _, apply bv_rw' (bv_symm $ this), simp, from ‹_›}, change _ ≤ (λ w, pair w₁ v₁ =ᴮ w) _,
       apply bv_rw' check_pair, simp, rw pair_eq_pair_iff,
       from ⟨‹_›,‹_›⟩ },
    { by_contra, suffices : Γ_5 ≤ ⊥, from false_of_bot_lt_and_le_bot ‹_› ‹_›, apply check_not_mem a,
      suffices : Γ_5 ≤ pair w₂ v₂ =ᴮ (pSet.pair (pSet.func x (check_cast iw₂)) (pSet.func y (check_cast iv₂)))̌ ,
      by {change _ ≤ (λ w, w ∈ᴮ f̌) _, apply bv_rw' (bv_symm $ this), simp, from ‹_›}, change _ ≤ (λ w, pair w₂ v₂ =ᴮ w) _,
       apply bv_rw' check_pair, simp, rw pair_eq_pair_iff,
       from ⟨‹_›,‹_›⟩ },
    { apply check_bv_eq_iff.mpr, tactic.rotate 1, from 𝔹, apply_instance,
      rw ←check_bv_eq_nonzero_iff_eq_top, from lt_of_lt_of_le H_lt (by bv_cc) },
end

@[simp]lemma eq_of_is_inj_of_eq {x y x' y' f : bSet 𝔹} {Γ : 𝔹} (H_is_inj : Γ ≤ is_inj f) (H_eq : Γ ≤ x' =ᴮ y')
  (H_mem₁ : Γ ≤ pair x x' ∈ᴮ f) (H_mem₂ : Γ ≤ pair y y' ∈ᴮ f) : Γ ≤ x =ᴮ y :=
H_is_inj x y x' y' (le_inf (le_inf ‹_› ‹_›) ‹_›)

-- lemma funext (f x y z : bSet 𝔹) {Γ : 𝔹} (H_func : Γ ≤ is_func f) (H : Γ ≤ (pair x y) ∈ᴮ f)
--   (H' : Γ ≤ (pair x z) ∈ᴮ f) : Γ ≤ y =ᴮ z :=
-- H_func x x y z (le_inf ‹_› ‹_›) (bv_refl)

-- ∀ z ∈ x, ∀ w ∈ y, (z,w) ∈ f ↔ (z,w) ∈ g

-- not really funext since it doesn't use extensionality in an essential way
lemma funext {x y f g : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ is_function x y f) (H₂ : Γ ≤ is_function x y g)
  (H_peq : Γ ≤ ⨅ p, p ∈ᴮ prod x y ⟹ (p ∈ᴮ f ⇔ p ∈ᴮ g)) : Γ ≤ f =ᴮ g :=
begin
  have H_sub₁ := subset_prod_of_is_function H₁, have H_sub₂ := subset_prod_of_is_function H₂,
  apply mem_ext, all_goals {bv_intro z, bv_imp_intro Hz_mem},
    { have := mem_of_mem_subset H_sub₁ Hz_mem, replace H_peq := H_peq z ‹_›,
      rw le_inf_iff at H_peq, cases H_peq with H_peq₁ H_peq₂, exact H_peq₁ Hz_mem },
    { have := mem_of_mem_subset H_sub₂ Hz_mem, replace H_peq := H_peq z ‹_›,
      rw le_inf_iff at H_peq, cases H_peq with H_peq₁ H_peq₂, exact H_peq₂ Hz_mem }
end

/-- A relation f is surjective if for every w ∈ y there is a v ∈ x such that (v,w) ∈ f. -/
@[reducible]def is_surj (x y : bSet 𝔹) (f : bSet 𝔹) : 𝔹 :=
⨅v, v ∈ᴮ y ⟹ (⨆w, w ∈ᴮ x ⊓ pair w v ∈ᴮ f)

/-- x is larger than y if there is a subset S ⊆ X which surjects onto y. -/
def larger_than (x y : bSet 𝔹) : 𝔹 := ⨆ S, ⨆f, S ⊆ᴮ x ⊓ (is_func' S y f) ⊓ (is_surj S y f)

lemma is_surj_empty {Γ : 𝔹} : Γ ≤ is_surj (∅ : bSet 𝔹) ∅ ∅ :=
forall_empty

lemma function_of_func'_is_function {x y f : bSet 𝔹} {Γ} (H_is_func' : Γ ≤ is_func' x y f) : Γ ≤ is_function x y (function_of_func' H_is_func') :=
begin
  refine le_inf (le_inf _ _) _,
    { exact is_func_subset_of_is_func (is_func_of_is_func' ‹_›) function_of_func'_subset },
    { bv_intro w₁, rw[<-deduction, inf_comm], let Γ_1 := w₁ ∈ᴮ x ⊓ Γ,
      change Γ_1 ≤ _, have H : Γ_1 ≤ w₁ ∈ᴮ x := by simp[Γ_1, inf_le_right],
      have : Γ_1 ≤ is_func' x y f := le_trans inf_le_right H_is_func',
      have H_total := bv_and.right this w₁ H, bv_cases_at H_total w₂ H_w₂,
      apply bv_use w₂, bv_split, refine le_inf ‹_› _,
      erw[mem_binary_inter_iff], simp* },
    { exact binary_inter_subset_right }
end

lemma function_of_func'_surj_of_surj {x y f : bSet 𝔹} {Γ} (H_is_func' : Γ ≤ is_func' x y f) (H_is_surj : Γ ≤ is_surj x y f) : Γ ≤ is_surj x y (function_of_func' H_is_func')  :=
begin
  bv_intro z, bv_imp_intro' Hz,
  have := H_is_surj z Hz, bv_cases_at' this w Hw,
  apply bv_use w, bv_split, refine le_inf ‹_› _,
  erw[mem_binary_inter_iff], simp*
end

lemma function_of_func'_inj_of_inj {x y f : bSet 𝔹} {Γ} {H : Γ ≤ is_func' x y f}
  (H_is_surj : Γ ≤ is_inj f) : Γ ≤ is_inj (function_of_func' H) :=
begin
  bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂,
  bv_imp_intro' H', bv_split_at H', bv_split_at H'_left,
  suffices : Γ_1 ≤ pair w₁ v₁ ∈ᴮ f ∧ Γ_1 ≤ pair w₂ v₂ ∈ᴮ f,
    by {refine H_is_surj w₁ w₂ v₁ v₂ _, simp*},
  refine ⟨_,_⟩; from mem_of_mem_subset (by {apply function_of_func'_subset, from ‹_›}) ‹_›
end

lemma surj_image { x y f : bSet 𝔹 } { Γ } (H_func : Γ ≤ is_func' x y f) : Γ ≤ is_surj x (image x y f) f :=
begin
  bv_intro w, bv_imp_intro H_mem,
  rw mem_image_iff at H_mem, cases H_mem with H_mem₁ H_mem₂,
  exact H_mem₂
end

lemma image_eq_codomain_of_surj {x y f : bSet 𝔹} {Γ} (H_surj : Γ ≤ is_surj x y f) : Γ ≤ image x y f =ᴮ y :=
begin
  refine subset_ext (by apply image_subset) _,
  rw subset_unfold', bv_intro z, bv_imp_intro Hz,
  rw mem_image_iff, exact ⟨‹_›,H_surj z ‹_›⟩
end

-- TODO: maybe move the S ⊆ᴮ x outside of the inner ⨆?
@[simp]lemma larger_than_domain_subset {Γ : 𝔹} {x y S : bSet 𝔹} (HS : Γ ≤ ⨆ f, S ⊆ᴮ x ⊓ (is_func' S y f) ⊓ (is_surj S y f))
  : Γ ≤ S ⊆ᴮ x :=
by {bv_cases_at HS f Hf, exact bv_and.left (bv_and.left ‹_›)}

def injects_into (x y : bSet 𝔹) : 𝔹 := ⨆f, (is_func' x y f) ⊓ is_inj f

def injection_into (x y : bSet 𝔹) : 𝔹 := ⨆f, is_injective_function x y f

lemma injection_into_of_injects_into {x y : bSet 𝔹} {Γ} (H : Γ ≤ injects_into x y) : Γ ≤ injection_into x y :=
begin
  bv_cases_at H f Hf, bv_split_at Hf,
  apply bv_use (function_of_func' Hf_left),
  refine le_inf _ _,
    { from function_of_func'_is_function _ },
    { from function_of_func'_inj_of_inj ‹_› }
end

lemma injects_into_of_injection_into {x y : bSet 𝔹} {Γ} (H_inj : Γ ≤ injection_into x y) : Γ ≤ injects_into x y :=
begin
  bv_cases_at H_inj f Hf, apply bv_use f, bv_split_at Hf,
  from le_inf (is_func'_of_is_function ‹_›) ‹_›
end

lemma injects_into_iff_injection_into {x y : bSet 𝔹} {Γ} : Γ ≤ injects_into x y ↔ Γ ≤ injection_into x y :=
⟨λ _, injection_into_of_injects_into ‹_›, λ _, injects_into_of_injection_into ‹_›⟩

lemma check_injects_into {x y : pSet.{u}} (H_inj : pSet.injects_into x y) {Γ : 𝔹} : Γ ≤ bSet.injects_into x̌ y̌ :=
begin
  cases H_inj with f H_f_inj, apply bv_use f̌,
  have : Γ ≤ _ := check_is_injective_function H_f_inj,
  change _ ≤ _ ⊓ _ at this,
  refine le_inf _ (bv_and.right ‹_›),
  from is_func'_of_is_function (bv_and.left ‹_›)
end

def surjects_onto (x y : bSet 𝔹) : 𝔹 := ⨆f, (is_func' x y f) ⊓ (is_surj x y f)

@[simp]lemma B_ext_larger_than_right {y : bSet 𝔹} : B_ext (λ z, larger_than y z) :=
by simp[larger_than]

@[simp]lemma B_ext_larger_than_left {y : bSet 𝔹} : B_ext (λ z, larger_than z y) :=
by simp[larger_than]

@[simp]lemma B_ext_injects_into_left {y : bSet 𝔹} : B_ext (λ z, injects_into z y) :=
by simp[injects_into]

@[simp]lemma B_ext_injects_into_right {y : bSet 𝔹} : B_ext (λ z, injects_into y z) :=
by simp[injects_into]

local infix `≺`:70 := (λ x y, -(larger_than x y))

local infix `≼`:70 := (λ x y, injects_into x y)

-- aka AC -- TODO
-- lemma injects_into_of_surjects_onto {x y : bSet 𝔹} {Γ} (H_inj : Γ ≤ surjects_onto x y) : Γ ≤ injects_into y x := sorry

section surjects_onto_of_larger_than

variables
  {x y : bSet 𝔹} {Γ : 𝔹}
  (H_larger_than : Γ ≤ larger_than x y)
  (H_nonempty : Γ ≤ exists_mem y )

section pointed_extension

variables {S f : bSet 𝔹} (b : bSet 𝔹) (H_b : Γ ≤ b ∈ᴮ y)
  (H_S : Γ ≤ S ⊆ᴮ x) (H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f)


include b H_S H_surj
def pointed_extension : bSet 𝔹 :=
subset.mk $ λ pr : (prod x y).type,
  (x.func pr.1 ∈ᴮ S ⟹ pair (x.func pr.1) (y.func pr.2) ∈ᴮ f) ⊓
  ((- (x.func pr.1 ∈ᴮ S)) ⟹ (y.func pr.2) =ᴮ b)

@[simp,cleanup]lemma pointed_extension_func {pr}
  : (pointed_extension b H_S H_surj).func pr = pair (x.func pr.1) (y.func pr.2) :=
by refl

lemma pointed_extension_bval {pr}
  : (pointed_extension b H_S H_surj).bval pr = ((x.func pr.1 ∈ᴮ S ⟹ pair (x.func pr.1) (y.func pr.2) ∈ᴮ f) ⊓
  ((- (x.func pr.1 ∈ᴮ S)) ⟹ (y.func pr.2) =ᴮ b)) ⊓ (prod x y).bval pr :=
by refl

@[simp]lemma pointed_extension_bval_of_mem {pr : (prod x y).type} (H_mem : Γ ≤ (x.func pr.1) ∈ᴮ S) (H_bval : Γ ≤ (pointed_extension b H_S H_surj).bval pr)
  : Γ ≤ x.bval pr.1 ∧ Γ ≤ y.bval pr.2 ∧ Γ ≤ pair (x.func pr.1) (y.func pr.2) ∈ᴮ f :=
begin
  simp [pointed_extension_bval] at H_bval, rcases H_bval with ⟨⟨H_bval₁, H_bval₂⟩, ⟨_,_⟩⟩,
  from ⟨‹_›,‹_›,H_bval₁ ‹_›⟩
end

@[simp]lemma pointed_extension_pair_mem_of_mem {i : x.type} {j : y.type} (H_mem : Γ ≤ (x.func i) ∈ᴮ S) (H_bval : Γ ≤ (pointed_extension b H_S H_surj).bval (i,j))
  : Γ ≤ pair (x.func i) (y.func j) ∈ᴮ f :=
(pointed_extension_bval_of_mem b H_S H_surj (by {change _ ≤ func x (i,j).fst ∈ᴮ _ at H_mem, from ‹_›}) ‹_›).right.right

@[simp]lemma pointed_extension_pair_mem_of_mem' {w v : bSet 𝔹} {pr : (prod x y).type} (H_mem : Γ ≤ (x.func pr.1) ∈ᴮ S) (H_bval : Γ ≤ (pointed_extension b H_S H_surj).bval pr) (H_eq : Γ ≤ pair w v =ᴮ func (pointed_extension b H_S H_surj) pr)
  : Γ ≤ pair w v ∈ᴮ f :=
begin
  simp at H_eq, apply @bv_rw' _ _ _ _ _ (H_eq) (λ z, z ∈ᴮ f), simp,
  cases pr with i j, apply pointed_extension_pair_mem_of_mem, repeat {assumption}
end
-- (pointed_extension_bval_of_mem b H_S H_surj (by {change _ ≤ func x (i,j).fst ∈ᴮ _ at H_mem, from ‹_›}) ‹_›).right.right

@[simp]lemma pointed_extension_bval_of_not_mem {pr : (prod x y).type} (H_mem : Γ ≤ - ((x.func pr.1) ∈ᴮ S)) (H_bval : Γ ≤ (pointed_extension b H_S H_surj).bval pr)
  : Γ ≤ x.bval pr.1 ∧ Γ ≤ y.bval pr.2 ∧ Γ ≤ (y.func pr.2) =ᴮ b :=
begin
  simp [pointed_extension_bval] at H_bval, rcases H_bval with ⟨⟨H_bval₁, H_bval₂⟩, ⟨_,_⟩⟩,
  from ⟨‹_›,‹_›,H_bval₂ ‹_›⟩
end

@[simp]lemma pointed_extension_y_eq_of_not_mem {i : x.type} {j : y.type} (H_mem : Γ ≤ - ((x.func i) ∈ᴮ S)) (H_bval : Γ ≤ (pointed_extension b H_S H_surj).bval (i,j))
  : Γ ≤ y.func j =ᴮ b :=
(pointed_extension_bval_of_not_mem b H_S H_surj (by {change _ ≤ - (func x (i,j).fst ∈ᴮ _) at H_mem, from ‹_›}) ‹_›).right.right

@[simp]lemma pointed_extension_y_eq_of_not_mem' {w v : bSet 𝔹} {pr : (prod x y).type} (H_mem : Γ ≤ - ((x.func pr.1) ∈ᴮ S)) (H_bval : Γ ≤ (pointed_extension b H_S H_surj).bval pr) (H_eq : Γ ≤ pair w v =ᴮ func (pointed_extension b H_S H_surj) pr)
  : Γ ≤ v =ᴮ b :=
begin
  simp at H_eq, replace H_eq := eq_of_eq_pair_right' H_eq, apply @bv_rw' _ _ _ _ _ (H_eq) (λ z, z =ᴮ b), simp,
  cases pr with i j, apply pointed_extension_y_eq_of_not_mem, repeat {assumption}
end

include H_b

variable {b}
lemma mem_pointed_extension_iff {w v : bSet 𝔹} (H_x_mem : Γ ≤ w ∈ᴮ x)
  : Γ ≤ pair w v ∈ᴮ pointed_extension b H_S H_surj
    ↔ (Γ ≤ ((w ∈ᴮ S ⊓ pair w v ∈ᴮ f) ⊔ (- (w ∈ᴮ S) ⊓ v =ᴮ b))) :=
begin
  refine ⟨_,_⟩; intro H,
    { bv_cases_on' (w ∈ᴮ S),
      { apply bv_or_left, refine le_inf ‹_› _,
        bv_split_at H_surj, have := is_total_of_is_func' H_surj_left w ‹_›,
        bv_cases_at this w₂ Hw₂, rw[mem_unfold'],
        apply bv_use (pair w w₂), rename H H', bv_split, refine le_inf ‹_› _,
        suffices this : Γ_2 ≤ v =ᴮ w₂,
          by {exact pair_congr (bv_refl) ‹_› },
        suffices this : Γ_2 ≤ pair w v ∈ᴮ f,
          by { apply eq_of_is_func_of_eq, repeat {assumption}, from bv_refl },

        rw[mem_unfold] at H', bv_cases_at H' pr Hpr,
        bv_split_at Hpr, apply pointed_extension_pair_mem_of_mem', repeat {assumption},
        {simp at Hpr_right, rw[pair_eq_pair_iff] at Hpr_right, cases Hpr_right, bv_cc},
        exact le_inf (le_inf ‹_› ‹_›) ‹_›
        },
      { apply bv_or_right, refine (le_inf ‹_› _) ,
        rw[mem_unfold] at H, bv_cases_at H pr Hpr, bv_split_at Hpr,
        apply pointed_extension_y_eq_of_not_mem', repeat {assumption},
        {simp at Hpr_right, rw[pair_eq_pair_iff] at Hpr_right, cases Hpr_right, rw[<-imp_bot],
         apply @bv_rw' _ _ _ _ _ (bv_symm Hpr_right_left) (λ z, z ∈ᴮ S ⟹ ⊥),
         {simp}, dsimp, rwa[imp_bot] },
         },
},
    { bv_or_elim_at' H,
      { bv_split_at H.left, bv_split_at H_surj,
        have := is_total_of_is_func' (H_surj_left) w H.left_left,
        bv_cases_at this v' Hv', have H_S' := H_S,
        rw[subset_unfold'] at H_S', replace H_S' := H_S' w ‹_›,
        rw[mem_unfold] at H_S',
        bv_cases_at H_S' i Hi,
        bv_split_at Hv', rw[mem_unfold] at Hv'_left, bv_cases_at Hv'_left j Hj,
        apply bv_use (i,j),
        refine le_inf _ _,
          { simp, refine ⟨⟨_,_⟩,_,_⟩,
              { bv_imp_intro H_good,
                  suffices this : Γ_5 ≤ pair w v' =ᴮ pair (func x i) (func y j) ,
                    by {apply @bv_rw' _ _ _ _ _ (bv_symm this) (λ z, z ∈ᴮ f), simp, from ‹_› },
                  refine pair_congr (bv_and.right ‹_›) (bv_and.right ‹_›) },
              { bv_imp_intro H_bad, refine bv_exfalso (bv_absurd _ H.left_left _),
                apply bv_rw' (bv_and.right Hi), simp, from ‹_› },
              { from bv_and.left Hi },
              { from bv_and.left Hj }
              },
          { refine pair_congr (bv_and.right ‹_›) _,
            suffices this : Γ_4 ≤ v =ᴮ v',
              by {bv_split_at Hj, bv_cc},
            apply eq_of_is_func'_of_eq, from ‹_›, from (bv_refl : _ ≤ w =ᴮ w), from ‹_›, from ‹_›
             },
       },
      { bv_split_at H.right,  rw[mem_unfold] at H_x_mem H_b,
        bv_cases_at H_x_mem i Hi, bv_split_at Hi,
        bv_cases_at H_b j Hj, bv_split_at Hj,
        apply bv_use (i,j), refine le_inf (le_inf _ (le_inf ‹_› ‹_›)) (pair_congr ‹_› (by bv_cc)),
        dsimp, refine le_inf _ _,
          { bv_imp_intro H_mem, refine bv_exfalso (bv_absurd _ H_mem _),
            apply @bv_rw' _ _ _ _ _ (bv_symm Hi_right) (λ z, - (z ∈ᴮ S)), simp, from ‹_› },
          { bv_imp_intro H_not_mem, from bv_symm ‹_› } } }
end

lemma pointed_extension_is_func : Γ ≤ is_func (pointed_extension b H_S H_surj) :=
begin
  bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂, bv_imp_intro' H,
  bv_imp_intro H_eq, bv_split_at H,
  rw[mem_unfold] at H_left H_right, bv_cases_at H_left pr₁ Hpr₁, bv_cases_at H_right pr₂ Hpr₂,
  cases pr₁ with i j, cases pr₂ with i' j',
  simp only with cleanup at Hpr₁ Hpr₂, bv_split_at Hpr₁, bv_split_at Hpr₂,
  rw[pair_eq_pair_iff] at Hpr₁_right Hpr₂_right, auto_cases,
  bv_cases_on ((x.func i) ∈ᴮ S) with H_mem,
    { suffices this : Γ_5 ≤ pair w₁ v₁ ∈ᴮ f ∧ Γ_5 ≤ pair w₂ v₂ ∈ᴮ f,
        by { exact eq_of_is_func'_of_eq (bv_and.left ‹_›) ‹_› this.left this.right },
      refine ⟨_,_⟩,
        { suffices : Γ_5 ≤ pair (x.func i) (y.func j) ∈ᴮ f,
            by { suffices H_eq : Γ_5 ≤ pair w₁ v₁ =ᴮ pair (x.func i) (y.func j) ,
                   by {apply @bv_rw' _ _ _ _ _ H_eq (λ z, z ∈ᴮ f), simp, from ‹_›},
                 from pair_congr ‹_› ‹_›, },
          apply pointed_extension_pair_mem_of_mem, repeat {assumption} },
        { suffices : Γ_5 ≤ pair (x.func i') (y.func j') ∈ᴮ f,
            by { suffices H_eq : Γ_5 ≤ pair w₂ v₂ =ᴮ pair (x.func i') (y.func j') ,
                   by {apply @bv_rw' _ _ _ _ _ H_eq (λ z, z ∈ᴮ f), simp, from ‹_›},
                 from pair_congr ‹_› ‹_›, },
          apply pointed_extension_pair_mem_of_mem, repeat {assumption},
          suffices h_eq : Γ_5 ≤ func x i' =ᴮ func x i,
            by {apply @bv_rw' _ _ _ _ _ h_eq (λ z, z ∈ᴮ S), simp, from ‹_›},
          by bv_cc } },
    { suffices this : Γ_5 ≤ v₁ =ᴮ b ∧ Γ_5 ≤ v₂ =ᴮ b,
        by { cases this with this₁ this₂, bv_cc },
      refine ⟨_,_⟩,
        { suffices : Γ_5 ≤ (y.func j) =ᴮ b,
            by { bv_cc },
          apply pointed_extension_y_eq_of_not_mem, repeat {assumption} },
        { suffices : Γ_5 ≤ (y.func j') =ᴮ b,
            by { bv_cc },
          suffices this : Γ_5 ≤ -(func x i' ∈ᴮ S),
            by {replace H_mem.right := this, apply pointed_extension_y_eq_of_not_mem, repeat{assumption}},
          suffices h_eq : Γ_5 ≤ func x i' =ᴮ func x i,
            by {apply @bv_rw' _ _ _ _ _ h_eq (λ z, - (z ∈ᴮ S)), simp, from ‹_›},
          bv_cc
           } },
end

lemma pointed_extension_is_total : Γ ≤ is_total x y (pointed_extension b H_S H_surj) :=
begin
  bv_intro a, bv_imp_intro' Ha,
  bv_cases_on (a ∈ᴮ S) with H_mem,
    { have := is_total_of_is_func' (bv_and.left (‹_› : Γ_2 ≤ _)),
      replace this := this a ‹_›, bv_cases_at this w₂ Hw₂,
      apply bv_use w₂, refine le_inf (bv_and.left ‹_›) _, have H_mem_x : Γ_3 ≤ a ∈ᴮ x := mem_of_mem_subset ‹_› ‹_›,
      apply (mem_pointed_extension_iff H_b ‹_› ‹_› ‹_›).mpr,
      apply bv_or_left, from le_inf ‹_› (bv_and.right ‹_›)
      },
    { apply bv_use b, refine le_inf ‹_› _, apply (mem_pointed_extension_iff H_b ‹_› ‹_› ‹_›).mpr,
      apply bv_or_right, from le_inf ‹_› (bv_refl) }
end

lemma pointed_extension_is_func' : Γ ≤ is_func' x y (pointed_extension b H_S H_surj) :=
begin
  refine le_inf _ _,
    { apply pointed_extension_is_func, from ‹_› },
    { apply pointed_extension_is_total, from ‹_› },
end

lemma pointed_extension_is_surj : Γ ≤ is_surj x y (pointed_extension b H_S H_surj) :=
begin
  bv_intro v, bv_imp_intro' Hv, bv_split_at H_surj, have H_surj' := H_surj_right,
  replace H_surj_right := H_surj_right v Hv,
  bv_cases_at H_surj_right w Hw, bv_split_at Hw,
  have H_mem_x := (mem_of_mem_subset H_S ‹_›),
  apply bv_use w, refine le_inf ‹_› _,
  apply (mem_pointed_extension_iff H_b ‹_› (le_inf ‹_› ‹_›) ‹_›).mpr,
  from bv_or_left (le_inf ‹_› ‹_›)
end

lemma pointed_extension_spec : Γ ≤ surjects_onto x y :=
begin
  apply bv_use (pointed_extension b H_S H_surj),
  from le_inf (by {apply pointed_extension_is_func', from ‹_›})
              (by {apply pointed_extension_is_surj, from ‹_›})
end

end pointed_extension

include H_larger_than H_nonempty

lemma surjects_onto_of_larger_than_and_exists_mem : Γ ≤ surjects_onto x y :=
begin
  bv_cases_at H_larger_than S HS, bv_cases_at HS f Hf, bv_split_at Hf,
  bv_split_at Hf_left,
  bv_cases_at H_nonempty b Hb,
  from pointed_extension_spec ‹_› ‹_› (le_inf ‹_› ‹_›)
end

end surjects_onto_of_larger_than

lemma larger_than_of_surjects_onto {x y : bSet 𝔹} {Γ} (H_surj : Γ ≤ surjects_onto x y) : Γ ≤ larger_than x y :=
begin
  apply bv_use x, unfold surjects_onto at H_surj, bv_cases_at H_surj f Hf,
  apply bv_use f, from le_inf (le_inf (by simp) (bv_and.left ‹_›)) (bv_and.right ‹_›)
end

-- lemma check_is_func {x y f : pSet.{u}} : pSet.is_func x y f ↔ ∀{Γ : 𝔹}, Γ ≤ is_function x̌ y̌ f̌   := sorry

lemma check_not_is_func {x y f : pSet.{u}} (H : ¬ pSet.is_func x y f) : ∀ {Γ : 𝔹}, ( Γ ≤ (is_function x̌ y̌ f̌) → Γ ≤ (⊥ : 𝔹)) :=
begin
  rw pSet.is_func_iff at H, intros Γ H', push_neg at H,
  bv_split_at H',
  cases H,
    { replace H := (check_not_subset H : Γ ≤ _),
      have := @bv_rw'' 𝔹 _ _ _ _ (check_prod) (λ z, - (f̌ ⊆ᴮ z)) H (by simp),
      dsimp only at this, bv_contradiction },
    { rcases H with ⟨z, ⟨Hz_mem, Hz⟩⟩,
      have H'_total := is_total_of_is_func' H'_left,
      replace H'_total := H'_total (ž) (by simp*), bv_cases_at H'_total w Hw,
      bv_split_at Hw, classical, by_contra H_nonzero,
      rw ←bot_lt_iff_not_le_bot at H_nonzero,
      rcases eq_check_of_mem_check ‹_› Hw_left with ⟨i, Γ', HΓ'_nonzero, HΓ'_le, Hi⟩,
      have Hz₁ := Hz (y.func i), cases Hz₁ with H_not_total H_not_func,
        { suffices this : Γ' ≤ ⊥, by exact false_of_bot_lt_and_le_bot HΓ'_nonzero ‹_›,
          refine check_not_mem H_not_total _,
          apply @bv_rw' _ _ _ _ _ check_pair (λ z, z ∈ᴮ f̌), simp, dsimp,
          apply @bv_rw' _ _ _ _ _ (bv_symm Hi) (λ w, pair ž w ∈ᴮ f̌), from B_ext_pair_mem_right,
          from le_trans HΓ'_le ‹_› },
        { rcases H_not_func with ⟨b, Hb_pair_mem, Hb_neq⟩,
          have H_not_eq : Γ' ≤ _ := check_not_eq Hb_neq,
          have H_is_func := is_func_of_is_func' H'_left ž ž w b̌ (le_inf ‹_› _) bv_refl,
          replace H_is_func := (le_trans HΓ'_le H_is_func : Γ' ≤ w =ᴮ b̌),
          refine false_of_bot_lt_and_le_bot HΓ'_nonzero (bv_absurd _ (bv_symm H_is_func) _),
          apply bv_rw' Hi, simp, from ‹_›,
          apply @bv_rw' _ _ _ _ _ (bv_symm check_pair) (λ w, w ∈ᴮ f̌), simp,
          exact check_mem Hb_pair_mem } },
end

-- lemma check_is_surj {x y f : pSet.{u}} : pSet.is_surj x y f ↔ ∀{Γ : 𝔹}, Γ ≤ is_surj x̌ y̌ f̌   :=
-- begin
--   sorry
-- end

lemma check_not_is_surj {x y f : pSet.{u}} (H : ¬ pSet.is_surj x y f) : ∀ {Γ : 𝔹}, Γ ≤  is_surj x̌ y̌ f̌ → Γ ≤ (⊥ : 𝔹) :=
begin
  unfold pSet.is_surj at H, push_neg at H,
  intros Γ H_surj,
  unfold is_surj at H_surj,
  rcases H with ⟨b, ⟨Hb₁, Hb₂⟩⟩ ,
  have := (check_mem Hb₁ : Γ ≤ _),
  replace H_surj := H_surj (b̌) this,
  rw[<-bounded_exists] at H_surj, swap, {change B_ext _, from B_ext_pair_mem_left },
  bv_cases_at H_surj i_a Hi_a, bv_split_at Hi_a,
  specialize Hb₂ (x.func (check_cast i_a)), cases Hb₂,
    { apply check_not_mem ‹_›, simp  },
    { rw ←pSet.pair_sound at Hb₂, change _ ∉ f at Hb₂, apply check_not_mem ‹_›,
      have this : Γ_1 ≤ (pSet.pair (pSet.func x (check_cast i_a)) b)̌  =ᴮ bSet.pair _ _,
      by {apply check_pair},
      apply @bv_rw' _ _ _ _ _ this (λ z, z ∈ᴮ f̌), simp, rwa[←check_func] }
end

lemma bot_lt_of_true {b : 𝔹} (H : ∀ {Γ}, Γ ≤ b) : ⊥ < b :=
by {specialize @H ⊤, rw top_le_iff at H, simp*}


section
variable {Γ : 𝔹}

/--
  Given a surjection f : x ↠ z and an injection g : y ↪ z, lift f along g to a surjection f' : x ↠ y.
-/
def lift_surj_inj {x z f g : bSet 𝔹} (y : bSet 𝔹) (H_surj : Γ ≤ is_surj x z f) (H_inj : Γ ≤ is_inj g) : bSet 𝔹 :=
@subset.mk _ _ (prod x y)
    (λ p, (⨆w, w ∈ᴮ z ⊓ (pair (x.func p.fst) w) ∈ᴮ f ⊓
                             (pair (y.func p.snd) w ∈ᴮ g)))

lemma ex_witness_of_mem_lift_surj_inj {x y z f g : bSet 𝔹} {w₁ w₂ : bSet 𝔹} {H_surj : Γ ≤ is_surj x z f}
  {H_inj : Γ ≤ is_inj g} (H_is_func'_f : Γ ≤ is_func' x z f) (H : Γ ≤ pair w₁ w₂ ∈ᴮ (lift_surj_inj y H_surj H_inj))
  : Γ ≤ ⨆ w, (w ∈ᴮ z ⊓ (pair w₁ w ∈ᴮ f) ⊓ (pair w₂ w ∈ᴮ g)) :=
begin
  bv_cases_at' H pr Hi, bv_split_at Hi, bv_split_at Hi_left,
    bv_cases_at' Hi_left_left w Hw, apply bv_use w, bv_split_at Hw, bv_split_at Hw_left,
    simp[pair_eq_pair_iff] at Hi_right, cases Hi_right with H₁ H₂,
    refine le_inf (le_inf ‹_› _) _,
    apply bv_rw' H₁, exact B_ext_pair_mem_left, from ‹_›,
    apply bv_rw' H₂, exact B_ext_pair_mem_left, from ‹_›
end

lemma mem_lift_surj_inj_iff {x y z f g : bSet 𝔹} {w₁ w₂ : bSet 𝔹} {H_surj : Γ ≤ is_surj x z f}
  {H_inj : Γ ≤ is_inj g} (H_is_func'_f : Γ ≤ is_func' x z f) {H_mem₁ : Γ ≤ w₁ ∈ᴮ x} {H_mem₂ : Γ ≤ w₂ ∈ᴮ y}
    : Γ ≤ pair w₁ w₂ ∈ᴮ (lift_surj_inj y H_surj H_inj) ↔ Γ ≤ ⨆ w, (w ∈ᴮ z ⊓ (pair w₁ w ∈ᴮ f) ⊓ (pair w₂ w ∈ᴮ g)) :=
begin
  refine ⟨_,_⟩; intro H,
    { apply ex_witness_of_mem_lift_surj_inj _ _, from x, from y, repeat {assumption} },

    { unfold lift_surj_inj, rw[mem_subset.mk_iff], bv_cases_at H w Hw, bv_split_at Hw, bv_split_at Hw_left,
      rw[mem_unfold] at H_mem₁, bv_cases_at H_mem₁ i Hi, rw[mem_unfold] at H_mem₂, bv_cases_at H_mem₂ j Hj,
      apply bv_use (i,j), refine le_inf _ _,
        { bv_split, simp[pair_congr, *] },
        { refine le_inf _ _,
          { apply bv_use w, refine le_inf (le_inf ‹_› _) _,
            bv_split_at Hi, apply @bv_rw' _ _ _ _ _ (bv_symm $ Hi_right) (λ x, pair x w ∈ᴮ f),
            exact B_ext_pair_mem_left, from ‹_›,
            bv_split_at Hj, apply @bv_rw' _ _ _ _ _ (bv_symm $ Hj_right) (λ x, pair x w ∈ᴮ g),
            exact B_ext_pair_mem_left, from ‹_› },
          { bv_split, simp* }}}
end
  -- refine ⟨_,_⟩; intro H,
  --   { unfold lift_surj_inj at H, rw[mem_unfold] at H, bv_cases_at H i Hi, dsimp at *,
  --     have Hi' := (bv_and.left $ bv_and.left Hi), bv_cases_at Hi' k Hk, apply bv_use (z.func k),
  --     refine le_inf (le_inf _ _) _,
  --       { sorry },
  --       { sorry },
  --       { sorry }},
  --  { sorry },

lemma lift_surj_inj_is_func {x y z f g : bSet 𝔹} {w₁ w₂ : bSet 𝔹} {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g} (H_is_func_f : Γ ≤ is_func' x z f) : Γ ≤ is_func (lift_surj_inj y H_surj H_inj) :=
begin
  bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂,
        bv_imp_intro' H_graph, rw[le_inf_iff] at H_graph, cases H_graph with H_gr₁ H_gr₂,
        bv_imp_intro H_eq, have H_inj₂ := H_inj, rw[is_inj] at H_inj₂,
        apply_at H_gr₁ (ex_witness_of_mem_lift_surj_inj H_is_func_f),
        apply_at H_gr₂ (ex_witness_of_mem_lift_surj_inj H_is_func_f),
        bv_cases_at H_gr₁ c₁ Hc₁, bv_cases_at H_gr₂ c₂ Hc₂,
        suffices c₁_eq_c₂ : _ ≤ c₁ =ᴮ c₂,
          by {clear_except H_inj Hc₁ Hc₂ c₁_eq_c₂,
              refine H_inj v₁ v₂ c₁ c₂ _, bv_split, bv_split,
              from le_inf (le_inf ‹_› ‹_›) ‹_› },
        refine (bv_and.left H_is_func_f) w₁ w₂ c₁ c₂ _ ‹_›,
        bv_split, bv_split, from le_inf ‹_› ‹_›, repeat {assumption},
end

lemma lift_surj_inj_is_total {y z f g S : bSet 𝔹} (H_surj : Γ ≤ is_surj S z f) (H_inj : Γ ≤ is_inj g) (H_is_func_f : Γ ≤ is_func' S z f)
  : Γ ≤ is_total (subset.mk (λ i : S.type, ⨆ b, b ∈ᴮ y ⊓ ⨆ c, c ∈ᴮ z ⊓ pair (S.func i) c ∈ᴮ f ⊓ pair b c ∈ᴮ g)) y (lift_surj_inj y H_surj H_inj) :=
begin
  bv_intro w₁, bv_imp_intro' Hw₁,
  rw[mem_subset.mk_iff] at Hw₁, bv_cases_at Hw₁ i Hi, have Hi' := (bv_and.left $ bv_and.right Hi),
  bv_cases_at Hi' b Hb, apply bv_use b, refine le_inf (bv_and.left Hb) _,
  apply (mem_lift_surj_inj_iff H_is_func_f).mpr, apply bv_rw' (bv_and.left Hi),
  {apply B_ext_supr, intro i, apply B_ext_inf, swap, simp, apply B_ext_inf, simp,
   exact B_ext_term (λ z, z ∈ᴮ f) (λ x, pair x i) },
  exact (bv_and.right Hb), from ‹_›, from ‹_›, rw[mem_unfold], apply bv_use i,
  exact le_inf (bv_and.right $ bv_and.right Hi) (bv_and.left Hi), exact bv_and.left Hb
end

lemma lift_surj_inj_is_surj {y z f g S : bSet 𝔹} (H_surj : Γ ≤ is_surj S z f) (H_inj : Γ ≤ is_inj g)
  (H_is_func_f : Γ ≤ is_func' S z f) (H_is_func_g : Γ ≤ is_func' y z g)
  : Γ ≤ is_surj (subset.mk (λ i : S.type, ⨆ b, b ∈ᴮ y ⊓ ⨆ c, c ∈ᴮ z ⊓ pair (S.func i) c ∈ᴮ f ⊓ pair b c ∈ᴮ g)) y (lift_surj_inj y H_surj H_inj) :=
begin
  bv_intro b, bv_imp_intro' Hb_mem, have := is_total_of_is_func' H_is_func_g b ‹_›,
  bv_cases_at this w₂ Hw₂, have := H_surj w₂ (bv_and.left Hw₂), bv_cases_at' this v Hv,
    bv_split_at Hv, rw[mem_unfold] at Hv_left, apply bv_use v,
    refine le_inf _ _,
      { rw[mem_subset.mk_iff], bv_cases_at' Hv_left i Hi, apply bv_use i,
        refine le_inf (bv_and.right Hi) (le_inf _ (bv_and.left Hi)),
          { apply bv_use b, refine le_inf ‹_› _, apply bv_use w₂,
            refine le_inf (le_inf (bv_and.left ‹_›) _) (bv_and.right ‹_›),
            have := (bv_symm $ bv_and.right Hi),
            apply @bv_rw' _ _ (func S i) v _ this (λ z, pair z w₂ ∈ᴮ f),
            swap, from ‹_›, apply B_ext_pair_mem_left }},
      { apply (mem_lift_surj_inj_iff H_is_func_f).mpr, apply bv_use w₂,
        exact le_inf (le_inf (bv_and.left Hw₂) ‹_›) (bv_and.right ‹_›),
        repeat {assumption}, dsimp [Γ_3], exact inf_le_left_of_le inf_le_left }
end

end

section
variable {Γ : 𝔹}
variables {x z f g : bSet 𝔹} (y : bSet 𝔹) (H_surj : Γ ≤ is_surj x z f) (H_inj : Γ ≤ is_inj g)
-- extends a surjection f : x ↠ z along an injection g : x ↪ y to a surjection
-- f' : y ↠ z

include H_surj H_inj
def extend_surj_inj : bSet 𝔹 :=
@subset.mk _ _ (prod y z)
    (λ p, (⨆w, w ∈ᴮ x ⊓ (pair w (z.func p.snd)) ∈ᴮ f ⊓
                          (pair w (y.func p.fst) ∈ᴮ g )))

variables {y} {H_surj} {H_inj}
lemma ex_witness_of_mem_extend_surj_inj {w₁ w₂ : bSet 𝔹}
  (H_is_func'_f : Γ ≤ is_func' x z f) (H : Γ ≤ pair w₁ w₂ ∈ᴮ (extend_surj_inj y H_surj H_inj))
  : Γ ≤ ⨆ w, (w ∈ᴮ x ⊓ (pair w w₁ ∈ᴮ g) ⊓ (pair w w₂ ∈ᴮ f)) :=
begin
  bv_cases_at' H pr Hi, bv_split_at Hi, bv_split_at Hi_left,
    bv_cases_at' Hi_left_left w Hw, apply bv_use w, bv_split_at Hw, bv_split_at Hw_left,
    simp[pair_eq_pair_iff] at Hi_right, cases Hi_right with H₁ H₂,
    refine le_inf (le_inf ‹_› _) _,
    apply bv_rw' H₁, exact B_ext_pair_mem_right, from ‹_›,
    apply bv_rw' H₂, exact B_ext_pair_mem_right, from ‹_›
end

lemma mem_extend_surj_inj_iff  {w₁ w₂ : bSet 𝔹} {H_mem₁ : Γ ≤ w₁ ∈ᴮ y} {H_mem₂ : Γ ≤ w₂ ∈ᴮ z}
  (H_is_func'_f : Γ ≤ is_func' x z f)
  : Γ ≤ pair w₁ w₂ ∈ᴮ (extend_surj_inj y H_surj H_inj) ↔ Γ ≤ ⨆ w, (w ∈ᴮ x ⊓ (pair w w₁ ∈ᴮ g) ⊓ (pair w w₂ ∈ᴮ f)) :=
begin
  refine ⟨_,_⟩; intro H,
    { exact ex_witness_of_mem_extend_surj_inj H_is_func'_f ‹_› },

    { unfold extend_surj_inj, rw[mem_subset.mk_iff], bv_cases_at H w Hw, bv_split_at Hw, bv_split_at Hw_left,
      rw[mem_unfold] at H_mem₁, bv_cases_at H_mem₁ i Hi, rw[mem_unfold] at H_mem₂, bv_cases_at H_mem₂ j Hj,
      apply bv_use (i,j), refine le_inf _ _,
        { bv_split, simp[pair_congr, *] },
        { refine le_inf _ _,
          { apply bv_use w, refine le_inf (le_inf ‹_› _) _,
            bv_split_at Hj, apply @bv_rw' _ _ _ _ _ (bv_symm $ Hj_right) (λ x, pair w x ∈ᴮ f),
            exact B_ext_pair_mem_right, from ‹_›,
            bv_split_at Hi, apply @bv_rw' _ _ _ _ _ (bv_symm $ Hi_right) (λ x, pair w x ∈ᴮ g),
            exact B_ext_pair_mem_right, from ‹_› },
          { bv_split, simp* }}}
end


variables (H_f_is_func' : Γ ≤ is_func' x z f) (H_g_is_func' : Γ ≤ is_func' x y g)
include H_f_is_func' H_g_is_func'
lemma extend_surj_inj_is_func : Γ ≤ is_func (extend_surj_inj y H_surj H_inj) :=
begin
  bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂,
  bv_imp_intro' H_mems, bv_split_at H_mems, bv_imp_intro H_eq,
  apply_at H_mems_left ex_witness_of_mem_extend_surj_inj ‹_›, tactic.rotate 1,
  repeat{assumption}, apply_at H_mems_right ex_witness_of_mem_extend_surj_inj ‹_›, tactic.rotate 1,
  repeat{assumption}, bv_cases_at H_mems_left w₁' Hw₁', bv_cases_at H_mems_right w₂' Hw₂',
  suffices H_eq' : Γ_4 ≤ w₁' =ᴮ w₂',
    by {apply eq_of_is_func'_of_eq, from ‹_›, from H_eq', all_goals {bv_split, from ‹_›} },
  apply eq_of_is_inj_of_eq ‹_› H_eq, all_goals {bv_split, bv_split, from ‹_›}
end

lemma extend_surj_inj_is_total : Γ ≤ is_total (image x y g) z (extend_surj_inj y H_surj H_inj) :=
begin
    bv_intro w₁, bv_imp_intro' Hw₁,
    have Hw₁_mem : _ ≤ w₁ ∈ᴮ y := mem_of_mem_subset image_subset Hw₁,
    rw image at Hw₁,
  rw[mem_subset.mk_iff] at Hw₁, bv_cases_at Hw₁ i Hi, have Hi' := (bv_and.left $ bv_and.right Hi),
  bv_cases_at Hi' b' Hb', bv_split_at Hb',
  have := is_total_of_is_func' H_f_is_func' b' Hb'_left, bv_cases_at this b Hb,
 apply bv_use b, refine le_inf (bv_and.left Hb) _,
  apply (mem_extend_surj_inj_iff H_f_is_func').mpr, apply bv_use b',
  refine le_inf (le_inf ‹_› _) (bv_and.right Hb),
  apply bv_rw' (bv_and.left Hi), exact B_ext_pair_mem_right,
  repeat {assumption}, exact bv_and.left ‹_›
end

lemma extend_surj_inj_is_surj : Γ ≤ is_surj (image x y g) z (extend_surj_inj y H_surj H_inj) :=
begin
  bv_intro b', bv_imp_intro' Hb'_mem,
  have := H_surj b' ‹_›, bv_cases_at this b Hb, bv_split_at Hb,
  have := is_total_of_is_func' H_g_is_func' b ‹_›,
  bv_cases_at' this w₂ Hw₂, bv_split_at Hw₂, apply bv_use w₂,
    refine le_inf _ _,
      { exact mem_image ‹_› ‹_› ‹_› },
      { apply (mem_extend_surj_inj_iff H_f_is_func').mpr, apply bv_use b,
        exact le_inf (le_inf ‹_› ‹_›) ‹_›, repeat{assumption} }
end

end

lemma bSet_lt_of_lt_of_le (x y z : bSet 𝔹) {Γ} (H₁ : Γ ≤ x ≺ y) (H₂ : Γ ≤ y ≼ z) : Γ ≤ x ≺ z :=
begin
  dsimp only [larger_than, injects_into] at ⊢ H₁ H₂,
  rw[<-imp_bot] at ⊢ H₁, bv_imp_intro H, refine H₁ _,
  bv_cases_at H S H_S, bv_cases_at H₂ g H_g,
  bv_cases_at H_S f Hf, bv_split, bv_split,
  apply bv_use (subset.mk (λ i : S.type, ⨆ b, b ∈ᴮ y ⊓ ⨆ c, c ∈ᴮ z ⊓ pair (S.func i) c ∈ᴮ f ⊓ pair b c ∈ᴮ g)),
  apply bv_use (lift_surj_inj y ‹_› ‹_›),
  refine le_inf (le_inf (subset_trans' subset.mk_subset ‹_›) (le_inf _ _)) _,
    { apply lift_surj_inj_is_func, repeat {assumption} },
    { exact lift_surj_inj_is_total Hf_right ‹_› ‹_› },
    { exact lift_surj_inj_is_surj Hf_right ‹_› ‹_› (le_inf ‹_› ‹_›) }
end

lemma bSet_lt_of_le_of_lt (x y z : bSet 𝔹) {Γ} (H₁ : Γ ≤ x ≼ y) (H₂ : Γ ≤ y ≺ z) : Γ ≤ x ≺ z :=
begin
  unfold larger_than at ⊢ H₂, rw[<-imp_bot], bv_imp_intro H, unfold injects_into at H₁,
  rw[<-imp_bot] at H₂, refine H₂ _,
  bv_cases_at H S HS, bv_cases_at HS f Hf, bv_cases_at H₁ g H_g,
  apply bv_use (image S y g), bv_split, bv_split_at Hf_left,
  apply bv_use (extend_surj_inj y ‹_› ‹_›),
  refine le_inf (le_inf (subset.mk_subset) (le_inf _ _)) _,
    { apply extend_surj_inj_is_func, from ‹_›,  exact is_func'_subset_of_is_func' H_g_left ‹_› },
    { apply extend_surj_inj_is_total, from ‹_›,  exact is_func'_subset_of_is_func' H_g_left ‹_›},
    { apply extend_surj_inj_is_surj, from ‹_›,  exact is_func'_subset_of_is_func' H_g_left ‹_› }
end

-- TODO
-- lemma larger_than_trans {x y z} {Γ : 𝔹} (H₁ : Γ ≤ larger_than x y) (H₂ : Γ ≤ larger_than y z)
--   : Γ ≤ larger_than x z :=
-- begin
--   bv_cases_at H₁ S HS, bv_cases_at H₂ S' HS', bv_cases_at HS f Hf, bv_cases_at HS' f' Hf',
--   apply bv_use (S ∩ᴮ (preimage S S' f)), sorry
-- end

section is_func'_comp
variables {x y z f g: bSet 𝔹} {Γ : 𝔹} (Hf_func : Γ ≤ is_func' x y f) (Hg_func : Γ ≤ is_func' y z g)

include Hf_func Hg_func

def is_func'_comp : bSet 𝔹 :=
subset.mk (λ pr : (prod x z).type, ⨆ b, b ∈ᴮ y ⊓ pair (x.func pr.1) b ∈ᴮ f ⊓ pair b (z.func pr.2) ∈ᴮ g)

lemma mem_is_func'_comp_iff {Γ'} {a c : bSet 𝔹} : Γ' ≤ pair a c ∈ᴮ is_func'_comp Hf_func Hg_func ↔ Γ' ≤ a ∈ᴮ x ∧ Γ' ≤ c ∈ᴮ z ∧ Γ' ≤ ⨆ b, b ∈ᴮ y ⊓ (pair a b ∈ᴮ f ⊓ pair b c ∈ᴮ g) :=
begin
  refine ⟨_,_⟩; intro H,
    { refine ⟨_,_,_⟩,
      { suffices : Γ' ≤ pair a c ∈ᴮ prod x z,
         by {rw mem_prod_iff at this, from this.left },
        refine mem_of_mem_subset (subset.mk_subset) H },
      { suffices : Γ' ≤ pair a c ∈ᴮ prod x z,
         by {rw mem_prod_iff at this, from this.right },
        refine mem_of_mem_subset (subset.mk_subset) H },
      { erw mem_subset.mk_iff₂ at H,
        bv_cases_at H pr Hpr, cases pr with i k,
        bv_split_at Hpr, bv_split_at Hpr_right, bv_cases_at Hpr_right_right b Hb,
        bv_split_at Hb, apply bv_use b, refine le_inf (bv_and.left ‹_›) _,
        erw pair_eq_pair_iff at Hpr_right_left,
        cases Hpr_right_left with H₁ H₂,
        refine le_inf _ _,
        apply bv_rw' H₁, from B_ext_pair_mem_left, from bv_and.right ‹_›,
        apply bv_rw' H₂, from B_ext_pair_mem_right, from ‹_› }},
    { erw mem_subset.mk_iff₂, rcases H with ⟨H_mem₁, H_mem₂, H⟩,
      rw mem_unfold at H_mem₁ H_mem₂, bv_cases_at H_mem₁ i Hi, bv_cases_at H_mem₂ k Hk,
      apply bv_use (i,k), refine le_inf (le_inf (bv_and.left ‹_›) (bv_and.left ‹_›)) (le_inf _ _),
      erw pair_eq_pair_iff, from ⟨bv_and.right ‹_›, bv_and.right ‹_›⟩,
      bv_cases_at H b Hb, bv_split_at Hb, apply bv_use b,
      bv_split_at Hi, bv_split_at Hk,
      refine le_inf (le_inf _ _) _,
        { from ‹_› },
        { apply @bv_rw' _ _ _ _ _ (bv_symm Hi_right) (λ w, pair w b ∈ᴮ f),
          from B_ext_pair_mem_left, from bv_and.left ‹_›  },
        { apply @bv_rw' _ _ _ _ _ (bv_symm Hk_right) (λ w, pair b w ∈ᴮ g),
          from B_ext_pair_mem_right, from bv_and.right ‹_› }}
end

lemma is_func'_comp_is_func : Γ ≤ is_func (is_func'_comp Hf_func Hg_func) :=
begin
  bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂, bv_imp_intro' H, bv_imp_intro H_eq,
  bv_split_at H, rw mem_is_func'_comp_iff at H_left H_right,
  rcases H_right with ⟨Hw₂_mem, Hv₂_mem, Hb₂⟩, rcases H_left with ⟨Hw₁_mem, Hv₁_mem, Hb₁⟩,
  bv_cases_at Hb₁ b₁ Hb₁', bv_split_at Hb₁', bv_cases_at Hb₂ b₂ Hb₂', bv_split_at Hb₂',
  bv_split_at Hb₁'_right, bv_split_at Hb₂'_right,
  refine (is_func_of_is_func' Hg_func b₁ b₂ v₁ v₂ (le_inf ‹_› ‹_›) _),
  from (is_func_of_is_func' Hf_func w₁ w₂ b₁ b₂ (le_inf ‹_› ‹_›) ‹_›)
end

lemma is_func'_comp_is_total : Γ ≤ is_total x z (is_func'_comp Hf_func Hg_func) :=
begin
  bv_intro a, bv_imp_intro' Ha, have := (is_total_of_is_func' Hf_func) a Ha,
  bv_cases_at this b Hb, bv_split_at Hb,
  have := (is_total_of_is_func' Hg_func) b Hb_left,
  bv_cases_at' this c Hc, bv_split_at Hc,
  apply bv_use c, refine le_inf ‹_› _,
  rw mem_is_func'_comp_iff, refine ⟨‹_›,‹_›,_⟩,
  apply bv_use b, from le_inf ‹_› (le_inf ‹_› ‹_›)
end

lemma is_func'_comp_is_func' : Γ ≤ is_func' x z (is_func'_comp Hf_func Hg_func) :=
le_inf (is_func'_comp_is_func _ _) (is_func'_comp_is_total _ _)

variables (Hf_inj : Γ ≤ is_inj f) (Hg_inj : Γ ≤ is_inj g)

include Hf_inj Hg_inj

lemma is_func'_comp_inj : Γ ≤ is_inj (is_func'_comp Hf_func Hg_func) :=
begin
  bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂, bv_imp_intro' H,
  bv_split_at H, bv_split_at H_left,
  rw mem_is_func'_comp_iff at H_left_left H_left_right,
  rcases H_left_left with ⟨Hw₁, Hv₁, Hb₁⟩, rcases H_left_right with ⟨Hw₂, Hv₂, Hb₂⟩,
  bv_cases_at Hb₁ b₁ Hb₁', bv_cases_at Hb₂ b₂ Hb₂', bv_split_at Hb₁', bv_split_at Hb₂',
  bv_split, refine Hf_inj w₁ w₂ b₁ b₂ _, refine le_inf (le_inf ‹_› ‹_›) _,
  from Hg_inj b₁ b₂ v₁ v₂ (le_inf (le_inf ‹_› ‹_›) ‹_›)
end

lemma is_func'_comp_surj (H₁ : Γ ≤ is_surj x y f) (H₂ : Γ ≤ is_surj y z g ) : Γ ≤ is_surj x z (is_func'_comp Hf_func Hg_func) :=
begin
  bv_intro wz, bv_imp_intro' Hwz_mem,
  replace H₂ :=  H₂ wz ‹_›, bv_cases_at H₂ wy Hwy,
  bv_split_at Hwy, replace H₁ := H₁ wy ‹_›,
  bv_cases_at H₁ wx Hwz, apply bv_use wx, refine le_inf (bv_and.left ‹_›) _,
  rw mem_is_func'_comp_iff, bv_split_at Hwz, refine ⟨‹_›,‹_›,_⟩,
  apply bv_use wy, bv_split_goal
end

end is_func'_comp

def function_comp {x y z f g : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ is_function x y f) (H₂ : Γ ≤ is_function y z g) : bSet 𝔹 :=
is_func'_comp (is_func'_of_is_function H₁) (is_func'_of_is_function H₂)

lemma function_comp_is_function {x y z f g : bSet 𝔹} {Γ : 𝔹} {H₁ : Γ ≤ is_function x y f} {H₂ : Γ ≤ is_function y z g} : Γ ≤ is_function x z (function_comp H₁ H₂) :=
begin
  refine le_inf _ _,
    { apply is_func'_comp_is_func' },
    { apply subset.mk_subset }
end

def injective_function_comp {x y z f g : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ is_injective_function x y f) (H₂ : Γ ≤ is_injective_function y z g) : bSet 𝔹 :=
is_func'_comp (is_func'_of_is_injective_function H₁) (is_func'_of_is_injective_function H₂)

lemma injective_function_comp_is_injective_function {x y z f g : bSet 𝔹} {Γ : 𝔹} {H₁ : Γ ≤ is_injective_function x y f} {H₂ : Γ ≤ is_injective_function y z g} : Γ ≤ is_injective_function x z (injective_function_comp H₁ H₂) :=
begin
  refine le_inf (by {apply function_comp_is_function; from bv_and.left ‹_›}) _,
  apply is_func'_comp_inj; from bv_and.right ‹_›
end

lemma injective_function_comp_is_function {x y z f g : bSet 𝔹} {Γ : 𝔹} {H₁ : Γ ≤ is_injective_function x y f} {H₂ : Γ ≤ is_injective_function y z g} : Γ ≤ is_function x z (injective_function_comp H₁ H₂) :=
bv_and.left (by apply injective_function_comp_is_injective_function)

lemma injects_into_trans {x y z} {Γ : 𝔹} (H₁ : Γ ≤ injects_into x y) (H₂ : Γ ≤ injects_into y z): Γ ≤ injects_into x z :=
begin
  bv_cases_at H₁ f Hf, bv_cases_at H₂ g Hg,
  bv_split_at Hf, bv_split_at Hg,
  apply bv_use (is_func'_comp Hf_left Hg_left),
  from le_inf (is_func'_comp_is_func' _ _) (is_func'_comp_inj _ _ Hf_right Hg_right)
end

lemma injection_into_trans {x y z} {Γ : 𝔹} (H₁ : Γ ≤ injection_into x y) (H₂ : Γ ≤ injection_into y z): Γ ≤ injection_into x z :=
by {rw ←injects_into_iff_injection_into at H₁ H₂ ⊢, from injects_into_trans H₁ H₂}

lemma AE_of_check_func_check₀ (x y : pSet.{u}) {f : bSet 𝔹} {Γ : 𝔹}
  (H : Γ ≤ is_func' (x̌) (y̌) f) (H_nonzero : ⊥ < Γ) :
  ∀ (i : x.type),
    ∃ (j : y.type),
      ⊥ < (is_func' (x̌) (y̌) f) ⊓ (pair ((x.func i)̌ ) ((y.func j)̌ )) ∈ᴮ f :=
begin
    intro i, have := is_total_of_is_func' H ((x.func i)̌ ) (by simp),
  have H' : Γ ≤ (is_func' (x̌) (y̌) f) ⊓ ⨆ w, w ∈ᴮ (y̌) ⊓ pair (x.func i)̌  w ∈ᴮ f ,
    by exact le_inf ‹_› ‹_›,
  rw[<-bounded_exists] at H', swap, {change B_ext _, exact B_ext_pair_mem_right},
  replace H' := lt_of_lt_of_le H_nonzero H', rw[inf_supr_eq] at H',
  cases y, dsimp at H', simp only [top_inf_eq] at H', exact (nonzero_wit H')
end

lemma AE_of_check_func_check (x y : pSet.{u}) {f : bSet 𝔹} {Γ : 𝔹}
  (H : Γ ≤ is_func' (x̌) (y̌) f) (H_nonzero : ⊥ < Γ) :
  Π (i : x.type),
    ∃ (j : y.type ) (Γ' : 𝔹) (H_nonzero' : ⊥ < Γ') (H_le : Γ' ≤ Γ),
      Γ' ≤ (is_func' (x̌) (y̌) f) ∧ Γ' ≤ (pair ((x.func i)̌ ) ((y.func j)̌ )) ∈ᴮ f :=
begin
    intro i, have := is_total_of_is_func' H ((x.func i)̌ ) (by simp),
  have H' : Γ ≤ (is_func' (x̌) (y̌) f) ⊓ ⨆ w, w ∈ᴮ (y̌) ⊓ pair (x.func i)̌  w ∈ᴮ f ,
    by exact le_inf ‹_› ‹_›,
  rw[<-bounded_exists] at H', swap, {change B_ext _, exact B_ext_pair_mem_right},
  rw[inf_supr_eq] at H',
  cases y, dsimp at H', simp only [top_inf_eq] at H',
  have := nonzero_wit' H_nonzero H', cases this with j Hj,
  use j, use is_func' x̌  (mk y_α (λ (a : y_α), (y_A a)̌ ) (λ (a : y_α), ⊤)) f ⊓
        pair (pSet.func x i)̌  (y_A j)̌  ∈ᴮ f ⊓ Γ,
  use ‹_›, refine ⟨inf_le_right,⟨_,_⟩⟩; tidy_context
end

-- lemma AE_of_check_func_check'
--  (x : pSet.{u})
--  {y f : bSet 𝔹}
--  {Γ : 𝔹}
--  (H : Γ ≤ is_func' x̌ y f)
--  (H_nonezero : ⊥ < Γ)
--    :  Π (i : x.type), ∃ (b : pSet.{u}) (Γ' : 𝔹) (H_nonzero' : ⊥ < Γ') (H_le : Γ' ≤ Γ),
--         Γ' ≤ is_func' x̌ y f ∧ Γ' ≤ pair (x.func i)̌  b̌ ∈ᴮ f :=
-- begin
--   intro i, have := is_total_of_is_func' H ((x.func i)̌ ) (by simp),
--   have H' : Γ ≤ (is_func' (x̌) y f) ⊓ ⨆ w, w ∈ᴮ y ⊓ pair (x.func i)̌  w ∈ᴮ f ,
--     by { exact le_inf ‹_› ‹_› },
--   rw[<-bounded_exists] at H', swap, {change B_ext _, exact B_ext_pair_mem_right},
--   rw[inf_supr_eq] at H', -- this is probably not true
--   cases y, dsimp at H', simp only [top_inf_eq] at H',
--   -- have := nonzero_wit' H_nonzero H', cases this with j Hj,
-- end

-- note: primed version of 𝔹-valued casing tactics will only note instead of replacing hypotheses
-- this circumvents dependency issues that occasionally pop up

lemma exists_surjection_of_surjects_onto {x y : bSet 𝔹} {Γ : 𝔹} (H_surj : Γ ≤ surjects_onto x y)
  : Γ ≤ ⨆ f, is_function x y f ⊓ is_surj x y f :=
begin
  bv_cases_at H_surj f' Hf',
  apply bv_use (function_of_func' $ bv_and.left Hf'),
  from le_inf (function_of_func'_is_function _) ( function_of_func'_surj_of_surj _ $ bv_and.right ‹_›),
end

def functions (x y : bSet 𝔹) : bSet 𝔹 :=
  set_of_indicator (λ s : (bv_powerset (prod x y) : bSet 𝔹).type, is_function x y ((bv_powerset (prod x y)).func s))

@[simp, cleanup] lemma functions_func {x y : bSet 𝔹} {i} : (functions x y).func i = (bv_powerset $ prod x y).func i := rfl

@[simp, cleanup] lemma functions_bval {x y : bSet 𝔹} {i} : (functions x y).bval i = is_function x y ((bv_powerset (prod x y)).func i) := rfl

@[simp, cleanup] lemma functions_type {x y : bSet 𝔹} : (functions x y).type = (bv_powerset (prod x y)).type := rfl

-- TODO(jesse) should be able to shorten this using subset.mk_mem_iff
lemma mem_functions_iff {g x y : bSet 𝔹} {Γ : 𝔹} : (Γ ≤ g ∈ᴮ functions x y) ↔ (Γ ≤ is_function x y g) :=
begin
  refine ⟨_,_⟩; intro H,
    { rw[mem_unfold] at H, bv_cases_at H s, bv_split,
      apply bv_rw' H_1_right, simp,
        dsimp[functions] at H_1_left, from ‹_›},
    { rw[mem_unfold], unfold is_function at H, bv_split, bv_split,
      have H_right' := bv_powerset_spec.mp H_right, rw[mem_unfold] at H_right',
      bv_cases_at H_right' s, apply bv_use s, bv_split, refine le_inf _ ‹_›,
      refine le_inf (le_inf _ _) ‹_›,
        {apply bv_rw' (bv_symm ‹_ ≤ g =ᴮ func (𝒫 prod x y) s›), simp, from ‹_›},
      -- TODO(jesse) why does apply fail to generate a motive for bv_rw'?
      bv_intro w₁, bv_imp_intro Hw₁, replace H_left_right := H_left_right w₁ ‹_›,
      bv_cases_at H_left_right w₂, apply bv_use w₂, bv_split, refine le_inf ‹_› _,
      apply bv_rw' (bv_symm ‹_ ≤ g =ᴮ func (𝒫 prod x y) s›), simp, from ‹_› }
end

-- lemma functions_check {x y : pSet.{u}} (pSet.functions x y):  := TODO(jesse): finish stating this


-- lemma function_reflect_AE {x y : pSet} {f : bSet 𝔹} (H : ⊤ ≤ is_function (x̌) (y̌) f) : ∀ i : x̌.type, ∃ j : y̌.type, ⊤ ≤ pair (x̌.func i) (y̌.func j) ∈ᴮ f :=
-- begin
--   bv_split, bv_split, rw[<-@bounded_forall] at H_left_right,
--   intro i, replace H_left_right := H_left_right i, simp at H_left_right,
--   rw[<-@bounded_exists] at H_left_right, simp at H_left_right,
--     { have this : ⊤ ≤ (⨆ i_x, pair (x̌.func i) (y̌.func i_x) ∈ᴮ (prod (x̌) (y̌))),
--         by {rw[<-top_le_iff] at H_left_right, apply bv_Or_imp,
--             show _ → _,
--               exact λ i_x, pair (x̌.func i) (y̌.func i_x) ∈ᴮ f,
--             rw[subset_unfold'] at H_right, dsimp,
--             bv_intro x_1, bv_imp_intro Hx_1,
--             replace H_right := H_right (pair (x̌.func i) (y̌.func x_1)) ‹_›,
--             apply bv_use (i, x_1), refine le_inf (by simp) bv_refl,
--             exact H_left_right},
--           sorry
--  },
--     { sorry },
--     { sorry }
-- end

-- /-- f is an injective function on x if it is a function and for every w₁ and w₂ ∈ x, if there exist v₁ and v₂ such that (w₁, v₁) ∈ f and (w₂, v₂) ∈ f,
--   then v₁ = v₂ implies  w₁ = w₂ -/
-- def is_inj_func (x y) (f : bSet 𝔹) : 𝔹 :=
--   is_func x y f ⊓ (⨅w₁ w₂, w₁ ∈ᴮ x ⊓ w₂ ∈ᴮ x ⟹
--     (⨆v₁ v₂, (pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⊓ v₁ =ᴮ v₂ ⟹ w₁ =ᴮ w₂)))

section function_mk'
variables   {x y : bSet 𝔹}
            (F : x.type → y.type)
            (χ : x.type → 𝔹)
            (H_ext : ∀ i j {Γ}, Γ ≤ x.func i =ᴮ x.func j → Γ ≤ y.func (F i) =ᴮ y.func (F j))
            (H_mem : ∀ i {Γ}, Γ ≤ x.bval i → Γ ≤ y.bval (F i) ∧ Γ ≤ χ i)

include H_ext H_mem
def function.mk' : bSet 𝔹 :=
subset.mk (λ pr : (prod x y).type, χ pr.1 ⊓ y.func pr.2 =ᴮ y.func (F pr.1))

@[simp, cleanup]lemma function.mk'_type
  : (function.mk' F χ H_ext H_mem).type = (prod x y).type := by refl

@[simp, cleanup]lemma function.mk'_func {pr}
  : (function.mk' F χ H_ext H_mem).func pr = (prod x y).func pr := by refl

@[simp, cleanup]lemma function.mk'_bval {pr}
  : (function.mk' F χ H_ext H_mem).bval pr = χ pr.1 ⊓
      y.func pr.2 =ᴮ y.func (F pr.1) ⊓ (prod x y).bval pr := by refl

@[simp, cleanup]lemma function.mk'_type_forall {ϕ : (function.mk' F χ H_ext H_mem).type → 𝔹} :
  (⨅(z: (function.mk' F χ H_ext H_mem).type), ϕ z) = ⨅(z : (prod x y).type), ϕ z :=
by refl

lemma function.mk'_is_func {Γ} : Γ ≤ is_func (function.mk' F χ H_ext H_mem) :=
begin
  bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂, bv_imp_intro H, bv_imp_intro H_eq,
  bv_split_at H, rw[mem_unfold] at H_left H_right,
  bv_cases_at H_left pr₁ Hpr₁, bv_cases_at H_right pr₂ Hpr₂,
  cases pr₁ with i j, cases pr₂ with i' j', simp at *, repeat{auto_cases},
  rw[pair_eq_pair_iff] at Hpr₁_right Hpr₂_right, auto_cases, -- floris, don't look at the tactic state
  have := @H_ext i i' Γ_4 (by bv_cc), bv_cc -- TODO(jesse): 𝔹-valued eblast?
end

lemma function.mk'_is_total {Γ} : Γ ≤ is_total x y (function.mk' F χ H_ext H_mem) :=
begin
  rw is_total_iff_is_total', bv_intro i, bv_imp_intro Hi,
  apply bv_use (F i), rw[mem_unfold,inf_supr_eq],
  apply bv_use (i, (F i)), simp*
end

lemma function.mk'_is_subset {Γ} : Γ ≤ (function.mk' F χ H_ext H_mem) ⊆ᴮ prod x y :=
begin
  rw[subset_unfold], simp only with cleanup, bv_intro pr, cases pr with i j, dsimp,
  bv_imp_intro H_bval, apply bv_use (i,j), simp [le_inf_iff] at *, tidy
end

lemma function.mk'_is_function {Γ} : Γ ≤ is_function x y (function.mk' F χ H_ext H_mem) :=
begin
  refine le_inf (le_inf _ _) _,
    { apply function.mk'_is_func },
    { apply function.mk'_is_total },
    { apply function.mk'_is_subset },
end

lemma function.mk'_is_inj {Γ} (H_inj : ∀ i j {Γ' : 𝔹}, Γ' ≤ y.func (F i ) =ᴮ y.func (F j) → Γ' ≤ x.func i =ᴮ x.func j) : Γ ≤ is_inj (function.mk' F χ H_ext H_mem) :=
begin
  bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂, bv_imp_intro H,
  bv_split_at H, bv_split_at H_left, bv_cases_at H_left_left pr₁ Hpr₁, bv_cases_at H_left_right pr₂ Hpr₂,
  dsimp at Hpr₁ Hpr₂, bv_split_at Hpr₁, bv_split_at Hpr₂, rw pair_eq_pair_iff at Hpr₁_right Hpr₂_right, cases Hpr₁_right, cases Hpr₂_right,
  cases pr₁ with i j, cases pr₂ with i' j', specialize @H_inj i i' Γ_3, bv_split, bv_split, dsimp at *,
  have := H_inj (by bv_cc), bv_cc
end


end function_mk'

section inj_inverse

variables {x y f : bSet 𝔹} {Γ : 𝔹} (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f)

include H_func H_inj

def inj_inverse : bSet 𝔹 :=
subset.mk (λ pr : (prod (image x y f) x).type, pair (x.func pr.2) ((image x y f).func pr.1) ∈ᴮ f)

lemma mem_inj_inverse_iff {Γ'} {b a : bSet 𝔹} : Γ' ≤ pair b a ∈ᴮ inj_inverse H_func H_inj ↔ Γ' ≤ a ∈ᴮ x ∧ Γ' ≤ b ∈ᴮ y ∧ Γ' ≤ pair a b ∈ᴮ f :=
begin
  refine ⟨_,_⟩; intro H,
    { unfold inj_inverse at H, rw mem_subset.mk_iff at H,
      refine ⟨_,_,_⟩,
        { bv_cases_at H pr Hpr, cases pr with i j, bv_split_at Hpr, erw pair_eq_pair_iff at Hpr_left,
          cases Hpr_left, simp at Hpr_right, change _ ≤ (λ w, w ∈ᴮ x) _, apply bv_rw' Hpr_left_right, simp,
          apply mem.mk'', from Hpr_right.right.right  },
        { bv_cases_at H pr Hpr, cases pr with i j, bv_split_at Hpr, erw pair_eq_pair_iff at Hpr_left,
          cases Hpr_left, simp at Hpr_right, change _ ≤ (λ w, w ∈ᴮ y) _, apply bv_rw' Hpr_left_left, simp,
          apply mem_of_mem_subset (image_subset) _, tactic.rotate 2, apply mem.mk'', from Hpr_right.right.left },
        { bv_cases_at H pr Hpr, cases pr with i j, bv_split_at Hpr, erw pair_eq_pair_iff at Hpr_left,
          cases Hpr_left, simp at Hpr_right, apply bv_rw' Hpr_left_right, from B_ext_pair_mem_left,
          apply bv_rw' Hpr_left_left, from B_ext_pair_mem_right, from Hpr_right.left  } },
    { erw mem_subset.mk_iff, rcases H with ⟨H₁, H₂, H₃⟩, rw mem_unfold at H₁ H₂,
      bv_cases_at H₁ i Hi, bv_cases_at H₂ j Hj, apply bv_use (j,i), refine le_inf _ _,
        { erw pair_eq_pair_iff, refine ⟨_,_⟩,
          { change _ ≤ _ =ᴮ y.func _, bv_split, bv_cc },
          { change _ ≤ _ =ᴮ x.func _, bv_split, bv_cc } },
        { refine le_inf _ _,
          {  bv_split_at Hi, bv_split_at Hj, simp,
             apply @bv_rw' _ _ _ _ _ (bv_symm Hi_right) (λ w, pair w ((y).func j) ∈ᴮ f), from B_ext_pair_mem_left,
             apply @bv_rw' _ _ _ _ _ (bv_symm Hj_right) (λ w, pair a w ∈ᴮ f), from B_ext_pair_mem_right,
             from ‹_›  },
          { bv_split, dsimp, refine le_inf (le_inf _ ‹_›) Hi_left,
            apply bv_use (func x i), refine le_inf (mem.mk'' ‹_›) _,
            apply @bv_rw' _ _ _ _ _ (bv_symm Hi_right) (λ w, pair w ((y).func j) ∈ᴮ f), from B_ext_pair_mem_left,
             apply @bv_rw' _ _ _ _ _ (bv_symm Hj_right) (λ w, pair a w ∈ᴮ f), from B_ext_pair_mem_right,
             from ‹_› }} }
end


lemma inj_inverse.is_func : Γ ≤ is_func (inj_inverse H_func H_inj) :=
begin
  bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂, bv_imp_intro' H,
  bv_split_at H, bv_imp_intro H_eq,
  rw mem_inj_inverse_iff at H_left H_right,
  repeat {auto_cases},
  refine H_inj v₁ v₂ w₁ w₂ _, bv_split_goal
end

lemma inj_inverse.is_total : Γ ≤ is_total (image x y f) x (inj_inverse H_func H_inj) :=
begin
  bv_intro z, bv_imp_intro' Hz, rw mem_image_iff at Hz, cases Hz with Hz₁ Hz₂,
  bv_cases_at Hz₂ z' Hz', apply bv_use z', refine le_inf _ _,
    { from bv_and.left ‹_› },
    { rw mem_inj_inverse_iff, from ⟨bv_and.left ‹_›, ‹_›, bv_and.right ‹_›⟩ }
end

lemma inj_inverse.is_func' : Γ ≤ is_func' (image x y f) x (inj_inverse H_func H_inj) :=
begin
  refine le_inf _ _,
    { apply inj_inverse.is_func },
    { apply inj_inverse.is_total },
end

lemma inj_inverse.is_surj : Γ ≤ is_surj (image x y f) x (inj_inverse H_func H_inj) :=
begin
  bv_intro z, bv_imp_intro' Hz_mem,
  have := is_total_of_is_func' H_func,
  replace this := this z Hz_mem, bv_cases_at this w₂ Hw₂, bv_split_at Hw₂,
  apply bv_use w₂, refine le_inf _ _,
    { rw mem_image_iff, refine ⟨‹_›, _⟩, apply bv_use z, from le_inf ‹_› ‹_› },
    { rw mem_inj_inverse_iff, from ⟨‹_›,‹_›,‹_›⟩ }
end

lemma inj_inverse.subset_prod : Γ ≤ inj_inverse H_func H_inj ⊆ᴮ prod (image x y f) x := by { apply subset.mk_subset }

lemma inj_inverse.is_function : Γ ≤ is_function (image x y f) x (inj_inverse H_func H_inj) :=
le_inf (by apply inj_inverse.is_func') (by apply inj_inverse.subset_prod)

lemma inj_inverse.is_inj : Γ ≤ is_inj (inj_inverse H_func H_inj) :=
begin
  bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂,
  bv_imp_intro' H, bv_split_at H, bv_split_at H_left,
  rw mem_inj_inverse_iff at H_left_left H_left_right,
  apply eq_of_is_func'_of_eq H_func H_right, tidy
end

end inj_inverse

section injective_function_inverse

def injective_function_inverse {x y f : bSet 𝔹} { Γ : 𝔹 } (H_inj : Γ ≤ is_injective_function x y f) : bSet 𝔹 :=
inj_inverse (is_func'_of_is_injective_function H_inj) (is_inj_of_is_injective_function H_inj)

lemma injective_function_inverse_is_injective_function { x y f : bSet 𝔹 } { Γ : 𝔹 } { H_inj : Γ ≤ is_injective_function x y f } : Γ ≤ is_injective_function (image x y f) x (injective_function_inverse H_inj) :=
le_inf (by apply inj_inverse.is_function) (by apply inj_inverse.is_inj)

lemma injective_function_inverse_is_inj { x y f : bSet 𝔹 } { Γ : 𝔹 } { H_inj : Γ ≤ is_injective_function x y f } : Γ ≤ is_inj (injective_function_inverse H_inj) := bv_and.right (by apply injective_function_inverse_is_injective_function)

end injective_function_inverse

section function_eval
variables { x y f : bSet 𝔹 } { Γ : 𝔹 } (H_func : Γ ≤ is_function x y f)

include H_func
noncomputable def function_eval (z : bSet 𝔹) (H_mem : Γ ≤ z ∈ᴮ x) : bSet 𝔹 :=
begin
  have H_total := (is_total_of_is_function H_func z ‹_›),
  exact classical.some (exists_convert H_total)
end

variable { H_func }

lemma function_eval_spec { z : bSet 𝔹 } { H_mem : Γ ≤ z ∈ᴮ x } : Γ ≤ (function_eval H_func z H_mem) ∈ᴮ y ⊓ pair z (function_eval H_func z H_mem) ∈ᴮ f :=
begin
  let p := _,
  change _ ≤ _ ⊓ pair z (classical.some p) ∈ᴮ _,
  exact classical.some_spec p
end

lemma function_eval_mem_codomain { z : bSet 𝔹 } { H_mem : Γ ≤ z ∈ᴮ x } : Γ ≤ (function_eval H_func z H_mem) ∈ᴮ y :=
bv_and.left (by apply function_eval_spec)

lemma function_eval_pair_mem { z : bSet 𝔹 } { H_mem : Γ ≤ z ∈ᴮ x } : Γ ≤ pair z (function_eval H_func z H_mem) ∈ᴮ f :=
bv_and.right (by apply function_eval_spec)

end function_eval


lemma surjects_onto_of_injects_into {x y : bSet 𝔹} {Γ} (H_inj : Γ ≤ injects_into x y) (H_exists_mem : Γ ≤ exists_mem x) : Γ ≤ surjects_onto y x :=
begin
  refine surjects_onto_of_larger_than_and_exists_mem _ ‹_›,
  bv_cases_at H_inj f Hf, bv_split_at Hf,
  apply bv_use (image x y f), apply bv_use (inj_inverse ‹_› ‹_›),
  refine le_inf (le_inf image_subset _) _, by apply inj_inverse.is_func',
  by apply inj_inverse.is_surj
end
-- section dom_cover

-- def dom_section : Π (x : bSet 𝔹), bSet 𝔹
-- | x@⟨α,A,B⟩ := function.mk' (check_shadow_cast_symm : x.type → (check_shadow x).type) (x.bval)
--     (by {intros i j Γ, apply B_congr_check_shadow}) (by {intros, simpa[*, check_shadow]})

-- def dom_cover : bSet 𝔹 := sorry -- use surjects_onto_of_injects_into

-- def dom_cover (x : bSet 𝔹) : bSet 𝔹 :=
-- function.mk' (check_shadow_cast : _ → x.type) (λ i, ⊤) _ _

/- by following lemma 1.52 in Bell, should be able to well-order any set
   via well-ordering principle in pSet -/

-- lemma dom_cover_surjection : is_surj (check_shadow )  :=

-- end dom_cover

def function.mk {u : bSet 𝔹} (F : u.type → bSet 𝔹) (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) : bSet 𝔹 :=
⟨u.type, λ a, pair (u.func a) (F a), u.bval⟩

@[simp, cleanup]lemma function.mk_type {u : bSet 𝔹} {F : u.type → bSet 𝔹} {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} : (function.mk F h_congr).type = u.type := by refl

@[simp, cleanup]lemma function.mk_func {u : bSet 𝔹} {F : u.type → bSet 𝔹} {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} {i} : (function.mk F h_congr).func i = pair(u.func i) (F i) := by refl

@[simp, cleanup]lemma function.mk_bval {u : bSet 𝔹} {F : u.type → bSet 𝔹} {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} {i} : (function.mk F h_congr).bval i = u.bval i := by refl

@[simp]lemma function.mk_self {u : bSet 𝔹} {F : u.type → bSet 𝔹} {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} {i : u.type} : u.bval i ≤ pair (u.func i) (F i) ∈ᴮ function.mk F h_congr :=
by {rw[mem_unfold], apply bv_use i, simp}

@[simp]lemma function.mk_self' {u : bSet 𝔹} {F : u.type → bSet 𝔹} {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j}  {i : u.type} : ⊤ ≤ u.bval i ⟹ pair (u.func i) (F i) ∈ᴮ function.mk F h_congr :=
by simp

/-- This is analogous to the check operation: we collect a type-indexed collection of bSets into a definite bSet -/
def check' {α : Type u} (A : α → bSet 𝔹) : bSet 𝔹 := ⟨α, A, λ x, ⊤⟩

@[simp, cleanup]def check'_type {α : Type u} {A : α → bSet 𝔹} : (check' A).type = α := by refl
@[simp, cleanup]def check'_bval {α : Type u} {A : α → bSet 𝔹} {i} : (check' A).bval i = ⊤ := by refl
@[simp, cleanup]def check'_func {α : Type u} {A : α → bSet 𝔹} {i} : (check' A).func i = A i := by refl

lemma mk_is_func {u : bSet 𝔹} (F : u.type → bSet 𝔹) (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) : ⊤ ≤ is_func (function.mk F h_congr) :=
begin
  bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂,
  bv_imp_intro H, bv_imp_intro H_eq,
  unfold function.mk at H, bv_split_at H,
  rw[mem_unfold] at H_left H_right,
  bv_cases_at H_left i Hi, bv_cases_at H_right j Hj,
  clear_except H_eq Hi Hj,
  simp[pair_eq_pair_iff] at Hi Hj, repeat{auto_cases},
  suffices : Γ_3 ≤ F i =ᴮ F j, by bv_cc,
  refine le_trans _ (h_congr i j), bv_cc
end

-- lemma mk_is_func' {u : bSet 𝔹} (F : u.type → bSet 𝔹) (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) {Γ} : Γ ≤ is_func' u (check' F) (function.mk F h_congr) := sorry

-- lemma mk_is_func {u : bSet 𝔹} (F : u.type → bSet 𝔹) (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) : ⊤ ≤ is_func u (check' F) (function.mk F h_congr) :=
-- begin
-- repeat{apply le_inf},
--   {bv_intro i, apply bv_imp_intro, have := @prod_mem 𝔹 _ u (check' F) (func u i) (F i),
--   apply le_trans _ this, apply le_inf, simp[mem.mk'], apply bv_use i, simp},

--   {bv_intro x, apply bv_imp_intro, bv_intro y, repeat{apply bv_imp_intro},
--    bv_intro v₁, bv_intro v₂, apply bv_imp_intro,
--    /- `tidy_context` says -/ apply poset_yoneda, intros Γ a, simp only [le_inf_iff] at a, cases a, cases a_right, cases a_left, cases a_left_left, cases a_left_left_left,
--    rw[mem_unfold] at a_right_left a_right_right,
--    bv_cases_at a_right_right i, specialize_context Γ,
--    bv_cases_at a_right_left j, specialize_context Γ_1,
--    clear a_right_right a_right_left,
--    bv_split_at a_right_left_1, bv_split_at a_right_right_1,
--    simp only with cleanup at a_right_left_1_1_1 a_right_right_1_1_1,
--    bv_mp a_right_right_1_1_1 (eq_of_eq_pair_left),
--    bv_mp a_right_right_1_1_1 (eq_of_eq_pair_right), -- TODO(jesse) generate sane variable names
--    bv_mp a_right_left_1_1_1 (eq_of_eq_pair_left),
--    bv_mp a_right_left_1_1_1 (eq_of_eq_pair_right),
--    have : Γ_2 ≤ func u i =ᴮ func u j, apply bv_trans, rw[bv_eq_symm],
--    assumption, rw[bv_eq_symm], apply bv_trans, rw[bv_eq_symm],
--    assumption, assumption, -- TODO(jesse) write a cc-like tactic to automate this
--    suffices : Γ_2 ≤ F i =ᴮ F j,
--     by {apply bv_trans, assumption, rw[bv_eq_symm], apply bv_trans,
--        assumption, from this},
--    apply le_trans this, apply h_congr}, -- the tactics are a success!
--   {bv_intro z, rw[<-deduction], rw[top_inf_eq], rw[mem_unfold], apply bv_Or_elim,
--    intro i_z, apply bv_use (F i_z), repeat{apply le_inf},
--      {tidy_context, rw[mem_unfold], apply bv_use i_z, apply le_inf, apply le_top, simp},
--      tidy_context, bv_mp a_right (subst_congr_pair_left), show bSet 𝔹, from (F i_z),
--      change Γ ≤ (λ w, w ∈ᴮ function.mk F h_congr) (pair z (F i_z)),
--      apply bv_rw' a_right_1, apply B_ext_mem_left, apply bv_use i_z, apply le_inf ‹_›,
--      simp[bv_eq_refl],
--      bv_intro w', repeat{apply bv_imp_intro}, tidy_context,
--      rw[mem_unfold] at a_left_right, bv_cases_at a_left_right i_w',
--      specialize_context Γ, bv_split_at a_left_right_1,
--      change _ ≤ (λv, (F i_z) =ᴮ v) w', apply bv_rw' a_left_right_1_1_1,
--      {simp[B_ext], intros x y, rw[inf_comm], apply bv_eq_trans},
--      change Γ_1 ≤ F i_z =ᴮ F i_w', simp only with cleanup at *,
--      bv_cases_at a_right i_pair, specialize_context Γ_1, bv_split_at a_right_1,
--      bv_mp a_right_1_1_1 (eq_of_eq_pair_left), bv_mp a_right_1_1_1 (eq_of_eq_pair_right),
--      bv_split_at a_left_right_1, clear a_right_1_1 a_right_1 a_left_right_1_1 a_left_right_1_2 a_right_1_1_1,
--      clear a_left_right_1 a_left_right a_left_left_left a_right,
--      have : Γ_2 ≤ F i_z =ᴮ F i_pair,
--        by {apply le_trans _ (h_congr _ _), apply bv_trans, rw[bv_eq_symm], from ‹_›, from ‹_›},
--      apply bv_trans, exact this, apply bv_trans, rw[bv_eq_symm], from ‹_›, from ‹_›}
-- end

lemma mk_inj_of_inj {u : bSet 𝔹} {F : u.type → bSet 𝔹} (h_inj : ∀ i j, i ≠ j → F i =ᴮ F j ≤ ⊥) (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) :
  ⊤ ≤ is_inj (function.mk F h_congr) :=
begin
  bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂, apply bv_imp_intro,
  rw[top_inf_eq], rw[mem_unfold, mem_unfold], rw[deduction],
  apply bv_cases_left, intro i, apply bv_cases_right, intro j, apply bv_imp_intro,
  simp,
  tidy_context,
    haveI : decidable (i = j) := classical.prop_decidable _,
    by_cases i = j,
      {subst h, have : Γ ≤ pair w₁ v₁ =ᴮ pair w₂ v₂, by apply bv_trans; {tidy},
       bv_mp this eq_of_eq_pair_left, from ‹_›},
    have := h_inj i j h, by_cases Γ = ⊥, rw[h], apply bot_le,
    suffices : Γ = ⊥, by contradiction,
    apply bot_unique,
    suffices : Γ ≤ F i =ᴮ F j, by {apply le_trans this ‹_›},
    bv_mp a_left_left_right eq_of_eq_pair_right,
    bv_mp a_left_right_right eq_of_eq_pair_right,
    from bv_trans (bv_symm ‹_›) (bv_trans a_right ‹_›)
end

-- lemma mk_inj_of_inj {u : bSet 𝔹} {F : u.type → bSet 𝔹} (h_inj : ∀ i j, i ≠ j → F i =ᴮ F j ≤ ⊥) (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) :
--   ⊤ ≤ is_inj_func u (check' F) (function.mk F h_congr) :=
-- begin
--   apply le_inf, apply mk_is_func,
--   bv_intro w₁, bv_intro w₂, apply bv_imp_intro, rw[top_inf_eq],
--   rw[mem_unfold, mem_unfold], apply bv_cases_left, intro i,
--   apply bv_cases_right, intro j, apply le_supr_of_le (F i),
--   apply le_supr_of_le (F j), apply bv_imp_intro,
--   tidy_context,
--     haveI : decidable (i = j) := by apply classical.prop_decidable,
--     by_cases i = j,
--       { subst h, apply bv_trans, tidy},
--     have := h_inj i j h,
--     by_cases Γ = ⊥, rw[h], apply bot_le,
--     suffices : Γ = ⊥, by contradiction,
--     apply bot_unique, from le_trans ‹_› this
-- end

lemma bot_of_mem_self {x : bSet 𝔹} : ⊤ ≤ (x ∈ᴮ x ⟹ ⊥) :=
begin
  induction x, simp[-imp_bot, bv_eq,mem], intro i, specialize x_ih i,
  apply bot_unique, apply bv_have_true x_ih, tidy_context,
  bv_mp a_left_left (show x_B i ≤ x_A i ∈ᴮ mk x_α x_A x_B, by apply mem.mk),
  change Γ ≤ (x_A i ∈ᴮ mk x_α x_A x_B) at a_left_left_1,
  have : Γ ≤ x_A i ∈ᴮ x_A i, rw[show Γ = Γ ⊓ Γ, by simp],
  apply le_trans, apply inf_le_inf, exact a_left_right, exact a_left_left_1,
  apply subst_congr_mem_right,
  have x_ih2 : Γ ≤ _ := le_trans (le_top) x_ih,
  exact context_imp_elim x_ih2 ‹_›
end

lemma bot_of_mem_self' {x : bSet 𝔹} {Γ} (H : Γ ≤ (x ∈ᴮ x)) : Γ ≤ ⊥ :=
begin
  have := @bot_of_mem_self 𝔹 _ x, rw[<-deduction, top_inf_eq] at this,
  from le_trans H this
end

lemma bot_of_zero_eq_one {Γ : 𝔹} (H : Γ ≤ 0 =ᴮ 1) : Γ ≤ ⊥ :=
bot_of_mem_self' $ by {apply bv_rw' H, simp, from zero_mem_one}

-- lemma bot_of_mem_mem_aux {x : bSet 𝔹} {i : x.type} : ⊤ ≤ ( x ∈ᴮ x.func i ⟹ ⊥) :=
-- begin
--   induction x, apply bv_imp_intro, rw[top_inf_eq], rw[mem_unfold],
--   apply bv_Or_elim, intro j,
--   specialize x_ih i, swap, exact j, tidy_context,
--   bv_mp a_left (show bval (func (mk x_α x_A x_B) i) j ≤ (func (func (mk _ _ _) i) j) ∈ᴮ func (mk _ _ _) i, by apply mem.mk'),
-- end

lemma bot_of_mem_mem (x y : bSet 𝔹) : ⊤ ≤ ((x ∈ᴮ y ⊓ y ∈ᴮ x) ⟹ ⊥) :=
begin
  induction x generalizing y, induction y,
  simp[-imp_bot, -top_le_iff, mem], apply bv_imp_intro, rw[top_inf_eq],
  apply bv_cases_right, intro a', apply bv_cases_left, intro a'',
  specialize x_ih a', tidy_context,
  specialize y_ih a'',
  bv_mp a_right_left (show x_B a' ≤ _ ∈ᴮ (mk x_α x_A x_B), by apply mem.mk),
  change Γ ≤ _ ∈ᴮ (mk x_α x_A x_B) at a_right_left_1,
  bv_mp a_left_left (show y_B a'' ≤ _ ∈ᴮ (mk y_α y_A y_B), by apply mem.mk),
  change Γ ≤ _ ∈ᴮ (mk y_α y_A y_B) at a_left_left_1,
  have this₁ : Γ ≤ x_A a' ∈ᴮ y_A a'', apply le_trans' a_right_left_1,
  apply le_trans, apply inf_le_inf, from a_left_right, refl,
  apply subst_congr_mem_right,
  have this₂ : Γ ≤ y_A a'' ∈ᴮ x_A a', apply le_trans' a_left_left_1,
  apply le_trans, apply inf_le_inf, from a_right_right, refl,
  apply subst_congr_mem_right,
  specialize x_ih (y_A a''), specialize_context_at x_ih Γ,
  bv_to_pi x_ih, apply x_ih, bv_split_goal
end

lemma bot_of_mem_mem' (x y : bSet 𝔹) {Γ} (H : Γ ≤ x ∈ᴮ y) (H' : Γ ≤ y ∈ᴮ x) : Γ ≤ ⊥ :=
begin
  have : Γ ≤ ((x ∈ᴮ y ⊓ y ∈ᴮ x) ⟹ ⊥),
    by {refine le_trans le_top (bot_of_mem_mem _ _) },
  exact this (le_inf ‹_› ‹_›)
end

end extras

section check
variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

-- lemma mem_check_mem_powerset_nonzero_iff {x : pSet} {S : (pSet.powerset x).type} {i : x.type} :
--   (⊥ : 𝔹) < (x.func i)̌  ∈ᴮ ((pSet.powerset x).func S)̌  ↔ (cast pSet.powerset_type S) i :=
-- begin
--   refine ⟨_,_⟩; intro H,
--     { sorry },
--     { sorry }
-- end

example {x : bSet 𝔹} {i : x.type} {χ : x.type → 𝔹} : χ i ≤ (x.func i) ∈ᴮ (set_of_indicator χ) :=
by {rw[mem_unfold], tidy_context, apply bv_use i, bv_split_goal}

lemma check_powerset_subset_powerset (x : pSet) {Γ : 𝔹} : Γ ≤ (pSet.powerset x)̌  ⊆ᴮ (bv_powerset (x̌))
:=
begin
  rw[subset_unfold], bv_intro s, simp only [mem, bval, top_imp, func, check, check_bval_top],
  suffices : ∃ χ : (x̌).type → 𝔹, Γ ≤ ((pSet.powerset x)̌ .func s) =ᴮ (set_of_indicator χ),
    by {cases this with χ Hχ, rw[mem_unfold], apply bv_use χ, refine le_inf _ ‹_›,
        { change _ ≤ _ ⊆ᴮ _, have := bv_rw' (bv_symm Hχ), show bSet 𝔹 → 𝔹,
          from λ z, z ⊆ᴮ x̌, from this, by simp,
          have eq_check_type : type ((p𝒫 x)̌ ) = pSet.type (p𝒫 x) :=
            by {simp, recover, all_goals{from ‹_›} },
          suffices this : (p𝒫 x).func (cast eq_check_type s) ⊆ x,
            by {convert check_subset this, cases x, refl},
          from pSet.mem_powerset.mp (by convert pSet.mem.mk (p𝒫 x).func _; from pSet.mk_eq)}},
   cases x with α A,
     use (λ i, Prop_to_bot_top (s i)),
   refine subset_ext _ _,
     { rw[subset_unfold], bv_intro j, bv_imp_intro Hj, simp,
       apply bv_use j.val,
       refine le_inf _ _,
         { have := j.property, unfold Prop_to_bot_top, simp* },
         { exact bv_refl }},
     { rw[subset_unfold], bv_intro j, bv_imp_intro Hj, simp,
       let Q := bval (set_of_indicator (λ (i : type $ (pSet.mk α A)̌  ), Prop_to_bot_top (s i))) j,
       haveI := classical.prop_decidable, by_cases H: ⊥ < Q,
         { suffices : s j,
             by { refine bv_use ⟨j, this⟩, swap,
                  simp*, transitivity ⊤,
                    { exact le_top },
                    { exact bv_refl }},
           by_contra, suffices this : Q = ⊥,
             by {rw[this] at H, simpa using H},
           dsimp[Q, Prop_to_bot_top], simp* },

         { rw[bot_lt_iff_not_le_bot] at H, push_neg at H,
           transitivity ⊥,
             { exact le_trans Hj H },
             { exact bot_le }}}
end

lemma check_functions_subset_functions {x y : pSet.{u}} {Γ : 𝔹} : Γ ≤ (pSet.functions x y)̌  ⊆ᴮ functions x̌ y̌ :=
begin
  rw subset_unfold', bv_intro w, bv_imp_intro Hw,
  rw mem_unfold at Hw, bv_cases_at Hw f Hf, bv_split_at Hf, rw check_func at Hf_right,
  let g := _, change _ ≤ w =ᴮ ǧ at Hf_right,
  suffices : pSet.is_func x y g,
    by {rw mem_functions_iff, apply bv_rw' Hf_right, simp, from check_is_func this },
  apply (pSet.mem_functions_iff _).mp, dsimp[g], apply pSet.mem.mk
end

@[simp]lemma check_mem' {y : pSet} {i : y.type} : ((y.func i)̌ ) ∈ᴮ y̌ = (⊤ : 𝔹) :=
by {apply top_unique, simp}

lemma of_nat_inj {n k : ℕ} (H_neq : n ≠ k) : ((of_nat n : bSet 𝔹) =ᴮ of_nat k) = ⊥ :=
check_bv_eq_bot_of_not_equiv (pSet.of_nat_inj ‹_›)

lemma of_nat_mem_of_lt {k₁ k₂ : ℕ} (H_lt : k₁ < k₂) {Γ} : Γ ≤ (bSet.of_nat k₁ : bSet 𝔹) ∈ᴮ (bSet.of_nat k₂) :=
check_mem $ pSet.of_nat_mem_of_lt H_lt

lemma check_succ_eq_succ_check {n : ℕ} : (of_nat (n.succ) : bSet 𝔹) = bSet.succ (of_nat n) :=
by simp[of_nat, succ, pSet.of_nat]

@[simp]lemma zero_eq_some_none {Γ : 𝔹} : Γ ≤ 0 =ᴮ two.func (some none) :=
bv_refl

end check

section powerset

parameters {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

parameter (x : bSet 𝔹)

local notation `fx2` := functions x 𝟚

def powerset_injects.F : (bv_powerset x).type → (functions x 𝟚).type :=
λ χ, λ pr, ((x.func pr.1 ∈ᴮ set_of_indicator χ ⊓ (𝟚.func (pr.2) =ᴮ 0)) ⊔ ((x.func pr.1) ∈ᴮ (subset.mk (λ i, - ((x.func i) ∈ᴮ set_of_indicator χ))) ⊓ (𝟚.func (pr.2) =ᴮ 1)))

lemma mem_powerset_injects.F_iff {Γ : 𝔹} {χ : x.type → 𝔹} {z : bSet 𝔹} : Γ ≤ pair z 0 ∈ᴮ func (functions x 𝟚) (powerset_injects.F χ) ↔ Γ ≤ z ∈ᴮ set_of_indicator χ :=
begin
  refine ⟨_,_⟩; intro H,
    { rw mem_unfold at H, bv_cases_at H pr Hpr, bv_split_at Hpr, cases pr with i j,
      erw pair_eq_pair_iff at Hpr_right, cases Hpr_right with Hpr_right.left Hpr_right.right, bv_or_elim_at Hpr_left,
      change _ ≤ (λ w, w ∈ᴮ set_of_indicator χ) _, apply bv_rw' Hpr_right.left, simp, from bv_and.left ‹_›,
      apply bv_exfalso, apply bot_of_zero_eq_one,
      have := bv_and.right Hpr_left.right, bv_cc},

    { bv_cases_at H i Hi, bv_split_at Hi,
      rw mem_unfold, apply bv_use (i, some none), refine le_inf _ _,
        { apply bv_or_left, refine le_inf _ _,
          { change _ ≤ (λ w, w ∈ᴮ (set_of_indicator χ)) _,
            apply bv_rw' (bv_symm Hi_right), simp, from ‹_› },
          { exact bv_refl }},
        { change _ ≤ pair _ _ =ᴮ pair _ _, simp [pair_eq_pair_iff, *] }}
end

lemma powerset_injects.F_ext : ∀ (i j : type (𝒫 x)) {Γ : 𝔹},
    Γ ≤ func (𝒫 x) i =ᴮ func (𝒫 x) j →
    Γ ≤ func (functions x 𝟚) (powerset_injects.F i) =ᴮ func (functions x 𝟚) (powerset_injects.F j) :=
begin
  intros χ₁ χ₂ Γ H,
  apply mem_ext; bv_intro z; bv_imp_intro Hz,
    { rw mem_unfold at Hz, bv_cases_at Hz ρ Hρ,
      rw[eq_iff_subset_subset, le_inf_iff] at H,
      cases ρ with i j,
      bv_split_at Hρ,
      cases H with H₁ H₂,
      bv_or_elim_at Hρ_left,
        { rename Hρ_left.left Hρ_left, bv_split_at Hρ_left,
      apply bv_use (i,j),
      refine le_inf (bv_or_left $ le_inf _ _) _, tactic.rotate 1,
      from ‹_›, from Hρ_right, refine mem_of_mem_subset H₁ ‹_›  },
        { rename Hρ_left.right Hρ_left, bv_split_at Hρ_left,
      apply bv_use (i,j),
      refine le_inf (bv_or_right $ le_inf _ _) _, tactic.rotate 1,
      from ‹_›, from Hρ_right,
      rw mem_subset.mk_iff at Hρ_left_left ⊢,
      bv_cases_at Hρ_left_left i' Hi',
      bv_split_at Hi',
      apply bv_use i', refine le_inf ‹_› _,
      rw ←imp_bot, refine le_inf _ (bv_and.right ‹_›),
      bv_imp_intro H',
      exact bv_absurd _ (mem_of_mem_subset H₂ ‹_›) (bv_and.left Hi'_right)},
 },
    {rw mem_unfold at Hz, bv_cases_at Hz ρ Hρ,
      rw[eq_iff_subset_subset, le_inf_iff] at H,
      cases ρ with i j,
      bv_split_at Hρ,
      cases H with H₁ H₂,
      bv_or_elim_at Hρ_left,
        { rename Hρ_left.left Hρ_left, bv_split_at Hρ_left,
      apply bv_use (i,j),
      refine le_inf (bv_or_left $ le_inf _ _) _, tactic.rotate 1,
      from ‹_›, from Hρ_right, refine mem_of_mem_subset H₂ ‹_›  },
        { rename Hρ_left.right Hρ_left, bv_split_at Hρ_left,
      apply bv_use (i,j),
      refine le_inf (bv_or_right $ le_inf _ _) _, tactic.rotate 1,
      from ‹_›, from Hρ_right,
      rw mem_subset.mk_iff at Hρ_left_left ⊢,
      bv_cases_at Hρ_left_left i' Hi',
      bv_split_at Hi',
      apply bv_use i', refine le_inf ‹_› _,
      rw ←imp_bot, refine le_inf _ (bv_and.right ‹_›),
      bv_imp_intro H',
      exact bv_absurd _ (mem_of_mem_subset H₁ ‹_›) (bv_and.left ‹_›)},
 }
end

lemma powerset_injects.F_subset_prod {χ : x.type → 𝔹} {Γ : 𝔹} {H_le : Γ ≤ set_of_indicator χ ⊆ᴮ x}
: Γ ≤ func (𝒫 prod x 𝟚) (powerset_injects.F χ) ⊆ᴮ prod x 𝟚 :=
begin
   change _ ≤ set_of_indicator _ ⊆ᴮ _, rw subset_unfold,
      bv_intro pr, bv_imp_intro H_pr, cases pr with i j,
      bv_or_elim_at H_pr,
        { rename H_pr.left H_pr, bv_split_at H_pr, have := mem_of_mem_subset H_le H_pr_left, rw mem_unfold at this,
      bv_cases_at this i' Hi, apply bv_use (i',j), simp, bv_split_at Hi, rw pair_eq_pair_iff,
      refine ⟨‹_›,_,bv_refl⟩, bv_cc },
        { rename H_pr.right H_pr, bv_split_at H_pr,
          rw mem_subset.mk_iff at H_pr_left,
          bv_cases_at H_pr_left i' Hi', bv_split_at Hi',
          rw mem_unfold, apply bv_use (i', j), refine le_inf _ _,
            { simp, from bv_and.right ‹_› },
            { erw pair_eq_pair_iff, refine ⟨‹_›, bv_refl⟩ }},
end

lemma powerset_injects.F_mem : ∀ (i : type (𝒫 x)) {Γ : 𝔹},
    Γ ≤ bval (𝒫 x) i → Γ ≤ bval (functions x 𝟚) (powerset_injects.F i) ∧ Γ ≤ ⊤ :=
begin
  intros χ Γ H_le, change _ ≤ (set_of_indicator χ) ⊆ᴮ x at H_le,
  refine ⟨_,le_top⟩, simp only with cleanup,
  refine le_inf (le_inf _ _) _,
    { bv_intro v₁, bv_intro v₂, bv_intro w₁, bv_intro w₂,
      bv_imp_intro H, bv_split_at H, bv_imp_intro H_eq,
      have := @powerset_injects.F_subset_prod _ _ x χ Γ_2 ‹_›,
      have H_pm_left := mem_of_mem_subset this H_left,
      have H_pm_right := mem_of_mem_subset this H_right,
      rw mem_prod_iff at H_pm_left H_pm_right,
      cases H_pm_left with Hv₁ Hw₁, cases H_pm_right with Hv₂ Hw₂,
      bv_cases_at H_left pr₁ Hpr₁, bv_cases_at H_right pr₂ Hpr₂,
      cases pr₁ with i₁ j₁, cases pr₂ with i₂ j₂,
      bv_split_at Hpr₁, bv_split_at Hpr₂,
      bv_or_elim_at Hpr₁_left; bv_or_elim_at Hpr₂_left,
        { erw pair_eq_pair_iff at Hpr₁_right Hpr₂_right,
          auto_cases, bv_split_at Hpr₁_left.left, bv_split_at Hpr₂_left.left, bv_cc },
        {bv_exfalso, refine bv_absurd _ (bv_and.left Hpr₁_left.left) _,
         bv_split_at Hpr₂_left.right, rw mem_subset.mk_iff at Hpr₂_left.right_left,
         bv_cases_at Hpr₂_left.right_left i Hi, bv_split_at Hi,
         suffices : Γ_7 ≤ x.func i₁ =ᴮ x.func i,
           by {apply @bv_rw' _ _ _ _ _ this (λ w, -(w ∈ᴮ set_of_indicator χ)), simp, from bv_and.left ‹_› },
         erw pair_eq_pair_iff at Hpr₁_right Hpr₂_right, auto_cases, bv_cc     },
        {bv_exfalso, refine bv_absurd _ (bv_and.left Hpr₂_left.left) _,
         bv_split_at Hpr₁_left.right, rw mem_subset.mk_iff at Hpr₁_left.right_left,
         bv_cases_at Hpr₁_left.right_left i Hi, bv_split_at Hi,
         suffices : Γ_7 ≤ x.func i₂ =ᴮ x.func i,
           by {apply @bv_rw' _ _ _ _ _ this (λ w, -(w ∈ᴮ set_of_indicator χ)), simp, from bv_and.left ‹_› },
         erw pair_eq_pair_iff at Hpr₁_right Hpr₂_right, auto_cases, bv_cc     },
        {  erw pair_eq_pair_iff at Hpr₁_right Hpr₂_right,
          auto_cases, bv_split_at Hpr₁_left.right, bv_split_at Hpr₂_left.right, bv_cc } },
    { bv_intro z, bv_imp_intro Hz, bv_cases_on z ∈ᴮ (set_of_indicator χ),
      {apply bv_use (0 : bSet 𝔹), rw le_inf_iff, refine ⟨_,_⟩,
        { from of_nat_mem_of_lt dec_trivial },
        { rw mem_unfold at Hz, bv_cases_at Hz i Hi, bv_split_at Hi,
          apply bv_rw' Hi_right, from B_ext_pair_mem_left,
          rw mem_unfold, apply bv_use (i, some none),
          refine le_inf _ _,
            { apply bv_or_left, refine le_inf _ _,
              { change _ ≤ (λ w, w ∈ᴮ set_of_indicator χ) _, apply bv_rw' (bv_symm Hi_right), simpa },
              { from bv_refl } },
            { erw pair_eq_pair_iff, simp* }}},
      {apply bv_use (1 : bSet 𝔹), rw le_inf_iff, refine ⟨_,_⟩,
        { from of_nat_mem_of_lt dec_trivial },
        { rw mem_unfold at Hz, bv_cases_at Hz i Hi, bv_split_at Hi,
          apply bv_rw' Hi_right, from B_ext_pair_mem_left,
          rw mem_unfold, apply bv_use (i, none),
          refine le_inf _ _,
            { apply bv_or_right, refine le_inf _ _,
              { dsimp only, let p := _, change _ ≤ _ ∈ᴮ p, change _ ≤ (λ w, w ∈ᴮ p) _, apply bv_rw' (bv_symm Hi_right), simp, dsimp only [p],
                rw mem_subset.mk_iff, apply bv_use i, refine le_inf ‹_› (le_inf _ ‹_›),
                  apply @bv_rw' _ _ _ _ _ (bv_symm Hi_right) (λ w, - (w ∈ᴮ set_of_indicator χ)), simp, from ‹_› },
              { from bv_refl },},
            { erw pair_eq_pair_iff, from ⟨by simp*, bv_refl⟩ }}}},
    apply powerset_injects.F_subset_prod, from ‹_›
end

lemma powerset_injects.F_inj : ∀ (i j : (𝒫 x).type) {Γ}, Γ ≤ (fx2).func (powerset_injects.F i ) =ᴮ (fx2).func (powerset_injects.F j) → Γ ≤ (𝒫 x).func i =ᴮ (𝒫 x).func j  :=
begin
  intros χ₁ χ₂ Γ H,
  apply mem_ext,
    { bv_intro z, bv_imp_intro Hz, erw ←mem_powerset_injects.F_iff at Hz,
     have := bv_rw'' H Hz, erw mem_powerset_injects.F_iff at this, exact this  },
    { bv_intro z, bv_imp_intro Hz, erw ←mem_powerset_injects.F_iff at Hz,
     have := bv_rw'' (bv_symm H) Hz, erw mem_powerset_injects.F_iff at this, exact this },
end

def powerset_injects.f : bSet 𝔹 := function.mk' powerset_injects.F (λ _, ⊤) powerset_injects.F_ext powerset_injects.F_mem

lemma powerset_injects_into_functions {x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ injects_into (bv_powerset x) (functions x 𝟚) :=
begin
  apply bv_use (powerset_injects.f x), refine le_inf _ _,
    { exact is_func'_of_is_function (function.mk'_is_function _ _ _ _) },
    { exact function.mk'_is_inj _ _ _ _ (powerset_injects.F_inj _) }
end

end powerset

section ordinals
variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

@[reducible]def epsilon_trichotomy (x : bSet 𝔹) : 𝔹 := (⨅y, y∈ᴮ x ⟹ (⨅z, z ∈ᴮ x ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y)))

@[reducible]def epsilon_well_founded (x : bSet 𝔹) : 𝔹 := (⨅u, u ⊆ᴮ x ⟹ (- (u =ᴮ ∅) ⟹ ⨆y, y∈ᴮ u ⊓ (⨅z', z' ∈ᴮ u ⟹ (- (z' ∈ᴮ y)))))

def epsilon_well_orders (x : bSet 𝔹) : 𝔹 :=
epsilon_trichotomy x ⊓ epsilon_well_founded x

@[reducible]def ewo (x : bSet 𝔹) : 𝔹 := epsilon_well_orders x

@[simp]lemma B_ext_ewo : B_ext (λ w : bSet 𝔹, epsilon_well_orders w) :=
by simp[epsilon_well_orders]

lemma epsilon_dichotomy (x y z : bSet 𝔹) : epsilon_well_orders x ≤ y ∈ᴮ x ⟹ (z ∈ᴮ x ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y)) :=
begin
  unfold epsilon_well_orders, apply bv_imp_intro, tidy_context,
  bv_to_pi', specialize a_left_left y, dsimp at a_left_left,
  bv_to_pi', specialize a_left_left ‹_›, bv_to_pi', exact a_left_left z
end

def is_transitive (x : bSet 𝔹) : 𝔹 := ⨅y, y∈ᴮ x ⟹ y ⊆ᴮ x

lemma subset_of_mem_transitive {x w : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ is_transitive x) (H₂ : Γ ≤ w ∈ᴮ x) : Γ ≤ w ⊆ᴮ x :=
by {bv_specialize_at H₁ w, bv_to_pi H₁_1, solve_by_elim}

@[simp] lemma B_ext_is_transitive : B_ext (is_transitive : bSet 𝔹 → 𝔹) :=
by {intros x y, unfold is_transitive, revert x y, change B_ext _, simp}

def Ord (x : bSet 𝔹) : 𝔹 := epsilon_well_orders x ⊓ is_transitive x

lemma epsilon_trichotomy_of_Ord {x a b : bSet 𝔹} {Γ} (Ha_mem : Γ ≤ a ∈ᴮ x) (Hb_mem : Γ ≤ b ∈ᴮ x) (H_Ord : Γ ≤ Ord x)
  : Γ ≤ a =ᴮ b ⊔ a ∈ᴮ b ⊔ b ∈ᴮ a :=
bv_and.left (bv_and.left H_Ord) a Ha_mem b Hb_mem

local infix `≺`:70 := (λ x y, -(larger_than x y))

local infix `≼`:70 := (λ x y, injects_into x y)

lemma injects_into_of_subset {x y : bSet 𝔹} {Γ} (H : Γ ≤ x ⊆ᴮ y) : Γ ≤ x ≼ y :=
begin
    refine bv_use _,
    {refine set_of_indicator _, show bSet 𝔹, exact prod x y,
     rintro ⟨a,b⟩, exact (x.func a) =ᴮ (y.func b) ⊓ x.bval a ⊓ y.bval b  },
    { refine le_inf _ _,
        { rw[is_func', is_func],
          refine le_inf _ _,
          { bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂,
            bv_imp_intro H', bv_imp_intro H_eq,
            bv_split, bv_cases_at H'_left p₁, bv_cases_at H'_right p₂,
            cases p₁ with i₁ i₂, cases p₂ with j₁ j₂,
            rename H'_left_1 H₁, rename H'_right_1 H₂,
            clear_except H₁ H₂ H_eq, simp only [le_inf_iff]  at H₁ H₂,
            repeat{auto_cases}, have := eq_of_eq_pair H₁_right, have := eq_of_eq_pair H₂_right,
            repeat{auto_cases}, bv_cc },

          {bv_intro w₁, bv_imp_intro w₁_mem_x, apply bv_use w₁,
           rw[subset_unfold'] at H, replace H := H w₁ ‹_›, refine le_inf ‹_› _,
           dsimp, rw[mem_unfold] at w₁_mem_x, rw[mem_unfold] at H,
           bv_cases_at w₁_mem_x i, bv_cases_at H j,
           apply bv_use (i,j), simp only [le_inf_iff],
           refine ⟨⟨⟨_,_⟩,_⟩,_⟩,
           refine bv_trans _ (bv_and.right H_1), apply bv_symm,
           exact bv_trans (bv_and.right w₁_mem_x_1) (bv_refl),
           exact bv_and.left w₁_mem_x_1, exact bv_and.left H_1,
           refine pair_congr _ _, exact bv_and.right w₁_mem_x_1, exact bv_and.right H_1}},

        { bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂, simp,
          bv_imp_intro, bv_split, bv_split,
            bv_cases_at H_1_left_left i, bv_cases_at H_1_left_right j,
            rcases i with ⟨i₁,i₂⟩, rcases j with ⟨j₁,j₂⟩,
            clear H_1_left_left H_1_left_right,
            bv_split, simp only [le_inf_iff] at H_1_left_right_1_left H_1_left_left_1_left,
            apply_all eq_of_eq_pair, repeat{auto_cases}, bv_cc }}
end

lemma bSet_le_of_subset {x y : bSet 𝔹} {Γ} (H : Γ ≤ x ⊆ᴮ y) : Γ ≤ x ≼ y :=
injects_into_of_subset H

lemma injection_into_of_subset {x y : bSet 𝔹} {Γ} (H : Γ ≤ x ⊆ᴮ y) : Γ ≤ injection_into x y :=
injects_into_iff_injection_into.mp $ injects_into_of_subset ‹_›

def Card (y : bSet 𝔹) : 𝔹 := Ord(y) ⊓ ⨅x, x ∈ᴮ y ⟹ (- larger_than y x)

lemma is_transitive_of_mem_Ord (y x : bSet 𝔹) : Ord x ⊓ y ∈ᴮ x ≤ (is_transitive y) :=
begin
  apply bSet.rec_on' y, clear y, intros y y_ih,

  bv_intro w, apply bv_imp_intro, rw[subset_unfold'], bv_intro z, apply bv_imp_intro, unfold Ord, tidy_context,
  bv_specialize_at a_left_left_left_right y, bv_imp_elim_at a_left_left_left_right_1 ‹_›,
  rw[subset_unfold'] at H, bv_specialize_at H w, bv_imp_elim_at H_1 ‹_›, bv_specialize_at a_left_left_left_right w,
  bv_imp_elim_at a_left_left_left_right_2 ‹_›, rw[subset_unfold'] at H_3,
  bv_specialize_at H_3 z, bv_imp_elim_at H_3_1 ‹_›, bv_mp a_left_left_left_left (epsilon_dichotomy x y z),
  bv_imp_elim_at a_left_left_left_left_1 ‹_›, bv_imp_elim_at H_5 ‹_›, bv_or_elim_at H_6, swap, assumption,
  bv_or_elim_at H_6.left,
  bv_exfalso, suffices : Γ_2 ≤ y ∈ᴮ w ⊓ w ∈ᴮ y,
    have : Γ_2 ≤ _ := le_trans (le_top) (bot_of_mem_mem y w),
    bv_imp_elim_at this ‹_›, assumption,
  apply le_inf, swap, assumption, apply bv_rw' H_6.left.left, simp,
  assumption,

  bv_exfalso,
  have a_left_right_old := a_left_right,
  rw[mem_unfold] at a_left_right, bv_cases_at a_left_right i_w, bv_split_at a_left_right_1,
  specialize y_ih i_w, rw[deduction] at y_ih,
  have := le_trans (le_inf ‹_› ‹_› : Γ_3 ≤ Ord x) ‹_›,
  have this' : Γ_3 ≤ func y i_w ∈ᴮ x,  rw[bv_eq_symm] at a_left_right_1_right,
  change Γ_3 ≤ (λ z, z ∈ᴮ x) (func y i_w), apply bv_rw' a_left_right_1_right,
  simp, from H_2, bv_imp_elim_at this ‹_›,
  have : Γ_3 ≤ is_transitive w, apply bv_rw' ‹_›, simp, from ‹_›,
  unfold is_transitive at this, have H_8 := this z ‹_›,
  rw[subset_unfold'] at H_8, bv_specialize_at H_8 y,
  bv_imp_elim_at H_8_1 ‹_›,
  suffices : Γ_3 ≤ y ∈ᴮ w ⊓ w ∈ᴮ y,
    have this3 := le_trans (@le_top _ _ Γ_3) (bot_of_mem_mem y w),
  bv_to_pi this3, apply this3, bv_split_goal
end

lemma is_ewo_of_mem_Ord (y x : bSet 𝔹) : Ord x ⊓ y ∈ᴮ x ≤ (epsilon_well_orders y) :=
begin
  bv_split_goal, rename i z, apply bv_imp_intro, bv_split_goal; rename i w, apply bv_imp_intro,

  all_goals{unfold Ord},
  {unfold epsilon_well_orders, tidy_context,
  bv_to_pi', specialize a_left_left_left_left_left w, dsimp at a_left_left_left_left_left,
  specialize a_left_left_left_right y,
    bv_to_pi a_left_left_left_right, specialize a_left_left_left_right ‹_›,
    rw[subset_unfold'] at a_left_left_left_right, bv_to_pi a_left_left_left_right,
    have H₁ := a_left_left_left_right w, bv_to_pi',
  have H₂ : Γ ≤ w ∈ᴮ x, from H₁ ‹_›,
  have H₃ : Γ ≤ z ∈ᴮ x,
    by {specialize a_left_left_left_right z, bv_to_pi', from a_left_left_left_right ‹_›},
  rename a_left_left_left_left_left H,
  replace H := H ‹_› z ‹_›,
  bv_or_elim_at H, bv_or_elim_at H.left,
  apply le_sup_left_of_le, apply le_sup_left_of_le, bv_split_goal,
  apply le_sup_right_of_le, assumption,
  apply le_sup_left_of_le, apply le_sup_right_of_le, assumption},

  {repeat{apply bv_imp_intro}, tidy_context,
  rename a_left_left_left_left H, rename i w,
  bv_split,
 have : Γ ≤ w ⊆ᴮ x,
   by {rw[subset_unfold'], bv_intro w', bv_imp_intro,
       have := mem_of_mem_subset a_left_right H,
       from mem_of_mem_subset (subset_of_mem_transitive ‹_› ‹_›) ‹_›},
 from H_right w ‹_› ‹_›}
end

theorem Ord_of_mem_Ord {x y : bSet 𝔹} {Γ : 𝔹} (H_mem : Γ ≤ x ∈ᴮ y) (H_Ord : Γ ≤ Ord y) : Γ ≤ Ord x :=
begin
  refine le_inf _ _,
    { have := is_ewo_of_mem_Ord x y, exact le_trans (le_inf H_Ord H_mem) ‹_› },
    { have := is_transitive_of_mem_Ord x y, exact le_trans (le_inf H_Ord H_mem) ‹_› }
end

open ordinal
open cardinal

noncomputable def ordinal.mk : ordinal.{u} → bSet 𝔹 := λ η,
limit_rec_on η ∅ (λ ξ mk_ξ, succ mk_ξ)
begin
  intros ξ is_limit_ξ ih,
  have this' : ξ = @ordinal.type (ξ.out).α (ξ.out).r (ξ.out).wo,
    by {rw[<-quotient.out_eq ξ], convert type_def _,
        rw[quotient.out_eq], cases quotient.out ξ, refl},
    refine ⟨ξ.out.α, _, λ x, ⊤⟩,
    intro x, apply ih, rw this', apply typein_lt_type _ x
end

@[simp]lemma ordinal.mk_zero : ordinal.mk 0 = (∅ : bSet 𝔹) := by simp[ordinal.mk]

@[simp]lemma ordinal.mk_succ (ξ ξ_pred : ordinal) (h : ξ = ordinal.succ ξ_pred) : (ordinal.mk ξ : bSet 𝔹) = succ (ordinal.mk ξ_pred) :=
by {simp[h, ordinal.mk]}

@[simp]lemma ordinal.mk_limit (ξ : ordinal) (h : is_limit ξ) : (ordinal.mk ξ : bSet 𝔹) =
⟨ξ.out.α, λ x, ordinal.mk (@typein _ (ξ.out.r) (ξ.out.wo) x), (λ x, ⊤)⟩ :=
by simp[*, ordinal.mk]

def lift_nat_Well_order : Well_order.{u} :=
{ α := ulift ℕ,
  r := (λ x y, x.down < y.down),
  wo :=
by {haveI this : (is_well_order ℕ (λ x y, x < y)) := by apply_instance, from { trichotomous := by {change ∀ a b : ulift ℕ, a.down < b.down ∨ a = b ∨ b.down < a.down, intros a b, have := this.trichotomous, specialize this a.down b.down, tidy, left, from ‹_›,
      right, right, from ‹_›},
    irrefl := by {intro a, apply this.irrefl},
    trans := by {intros a b c, apply this.trans},
    wf := by {have := this.wf, split, cases this with H, intro a, specialize H a.down,
              induction a, induction a, split, intros y H', cases H', cases H,
              specialize H_h a_n (by {change a_n < a_n + 1, simp, exact dec_trivial}),
              specialize a_ih H_h,
              split, intros y H', by_cases y.down = a_n,
              subst h, split, intros y' H'', cases a_ih, exact a_ih_h y' H'',

              have h' : y.down < a_n,
                by {have := this.trichotomous, specialize this y.down a_n, simp[*, -this] at this, suffices this' : ¬ a_n < y.down, by {simp[*,-this] at this; assumption}, intro H,
             from nat.lt_irrefl _ (lt_of_lt_of_le H (nat.le_of_lt_succ H'))},

              cases a_ih, from a_ih_h y h'}}}}

lemma lift_nat_Well_order_iso_nat : lift_nat_Well_order.r ≃o (λ x y : ℕ, x < y) :=
{to_fun := ulift.down,
  inv_fun := ulift.up,
  left_inv := by tidy,
  right_inv := by tidy,
  ord := by tidy}

noncomputable lemma order_isomorphism_of_equiv {X Y : Well_order.{u}} (H : X ≈ Y) : X.r ≃o Y.r :=
begin
  apply classical.choice, cases X, cases Y, apply type_eq.mp, from (quotient.sound H)
end

lemma order_iso_trans {α β γ} {X : α → α → Prop} {Y : β → β → Prop} {Z : γ → γ → Prop} (H₁ : X ≃o Y) (H₂ : Y ≃o Z) : X ≃o Z :=
H₁.trans H₂

lemma order_iso_symm {α β} {X : α → α → Prop} {Y : β → β → Prop} (H : X ≃o Y) : Y ≃o X :=
H.symm

-- noncomputable lemma omega_out_iso_nat : ordinal.omega.out.r ≃o ((λ x y : ℕ, x < y)) :=
-- begin
--   have this₁ := order_isomorphism_of_equiv (@quotient.mk_out (Well_order) _ lift_nat_Well_order),
--   have this₂ := (lift_nat_Well_order_iso_nat),
--   apply order_iso_trans _ this₂, apply order_iso_trans _ this₁,

--   sorry
-- end

-- lemma mk_omega_eq_omega : ⊤ ≤ ordinal.mk ordinal.omega =ᴮ (bSet.omega : bSet 𝔹) :=
-- begin
--   rw[ordinal.mk_limit ordinal.omega omega_is_limit], apply le_inf, swap,

--   {simp[-top_le_iff], intro k, induction k, induction k, simp,
--    repeat{sorry}},
--   {sorry}
-- end

lemma check_is_transitive {x : pSet} (H : pSet.is_transitive x) {Γ} : Γ ≤ is_transitive (x̌ : bSet 𝔹) :=
begin
  bv_intro y, bv_imp_intro,
  unfold pSet.is_transitive at H, rw[mem_unfold] at H_1,
  cases x, dsimp at H_1, bv_cases_at H_1 i_y, bv_split,
  apply bv_rw' H_1_1_right, simp, specialize H (x_A i_y) (by apply pSet.mem.mk),
  apply check_subset ‹_›
end

lemma check_ewo_left {x : pSet} (H : pSet.epsilon_well_orders x) {Γ : 𝔹} : Γ ≤ (⨅y, y∈ᴮ x̌ ⟹
  (⨅z, z ∈ᴮ x̌ ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y))) :=
begin
  bv_intro y, bv_imp_intro, bv_intro z, bv_imp_intro,
  rw[mem_unfold] at H_1 H_2, cases x, dsimp at H_1 H_2,
  bv_cases_at H_2 i_z, bv_cases_at H_1 i_y, bv_split,
  specialize H_left (x_A i_y) (by apply pSet.mem.mk) (x_A i_z) (by apply pSet.mem.mk),
  rename H_left this, repeat{cases this},
  apply le_sup_left_of_le, apply le_sup_left_of_le,
  apply bv_rw' H_2_1_right, simp, apply bv_rw' H_1_1_right, simp, from check_bv_eq ‹_›,

  apply le_sup_left_of_le, apply le_sup_right_of_le, apply bv_rw' H_2_1_right,
  simp, apply bv_rw' H_1_1_right, simp, from check_mem ‹_›,

  apply le_sup_right_of_le, apply bv_rw' H_2_1_right, simp, apply bv_rw' H_1_1_right, simp,
  from check_mem ‹_›
end

lemma check_ewo_right {x : pSet} (H : pSet.epsilon_well_orders x) {Γ : 𝔹} : Γ ≤ (⨅u, u ⊆ᴮ x̌ ⟹ (- (u =ᴮ ∅) ⟹ ⨆y, y∈ᴮ u ⊓ (⨅z', z' ∈ᴮ u ⟹ (- (z' ∈ᴮ y))))) :=
begin
  bv_intro u, bv_imp_intro, bv_imp_intro, cases H,
  rw[subset_unfold'] at H_1, apply bSet_axiom_of_regularity, from ‹_›
end

lemma check_ewo {x : pSet} (H : pSet.epsilon_well_orders x) {Γ} : Γ ≤ epsilon_well_orders (x̌ : bSet 𝔹) :=
le_inf (check_ewo_left ‹_›) (check_ewo_right ‹_›)

@[simp]lemma check_Ord {x : pSet} (H : pSet.Ord x) {Γ} : Γ ≤ Ord (x̌ : bSet 𝔹) :=
le_inf (check_ewo H.left) (check_is_transitive H.right)

@[simp]lemma Ord_card_ex (κ : cardinal) {Γ : 𝔹} : Γ ≤ Ord ((pSet.card_ex κ)̌ ) :=
by simp[pSet.card_ex]

def closed_under_successor (Γ) (x : bSet 𝔹) := Γ ≤ ⨅y, y ∈ᴮ x ⟹ succ y ∈ᴮ x

def omega_spec (ω : bSet 𝔹) := (∀ {Γ : 𝔹}, closed_under_successor Γ ω) ∧ ∀ (x : bSet 𝔹) {Γ} (H₁ : Γ ≤ ∅ ∈ᴮ x) (H₂ : closed_under_successor Γ x), Γ ≤ bSet.omega ⊆ᴮ x

lemma omega_closed_under_succ {Γ : 𝔹} : closed_under_successor Γ (bSet.omega) :=
begin
  unfold closed_under_successor, bv_intro y, bv_imp_intro H_mem,
  bv_cases_at H_mem k, cases k with k, simp at H_mem_1, refine bv_use _,
  exact (ulift.up $ k + 1), simp, apply bv_rw' H_mem_1,
    { exact @B_ext_term 𝔹 _ (λ z, z =ᴮ ((k+1)̃ ̌)) succ (by simp) (by simp) },
      -- TODO(jesse): automate calculation of the motive
    { simp[pSet.of_nat, succ] },
end

lemma omega_is_omega : omega_spec (bSet.omega : bSet 𝔹) :=
begin
  refine ⟨by apply omega_closed_under_succ, _⟩,
    {intros x Γ H₁ H₂, unfold closed_under_successor at H₂, rw[subset_unfold],
     simp, intro k, cases k, induction k, convert H₁,
     {change (∅̌) = _, simp},
     {let A := _, change Γ ≤ A ∈ᴮ x at k_ih,
      convert H₂ A ‹_›, from check_succ_eq_succ_check}}
end

lemma Ord_omega {Γ : 𝔹} : Γ ≤ Ord (omega) :=
le_inf (check_ewo pSet.is_ewo_omega) (check_is_transitive pSet.is_transitive_omega)

lemma Ord_of_nat {Γ : 𝔹} {n : ℕ} : Γ ≤ Ord (of_nat n) := Ord_of_mem_Ord of_nat_mem_omega Ord_omega

lemma Ord_one { Γ : 𝔹 } : Γ ≤ Ord 1 := Ord_of_nat

lemma Ord_zero { Γ : 𝔹 } : Γ ≤ Ord 0 := Ord_of_nat

lemma of_nat_subset_omega {n : ℕ} {Γ : 𝔹} : Γ ≤ of_nat n ⊆ᴮ omega :=
subset_of_mem_transitive (bv_and.right Ord_omega) of_nat_mem_omega

/-- ℵ₁ is defined as: the least ordinal which does not inject into ω -/
@[reducible]def aleph_one_Ord_spec (x : bSet 𝔹) : 𝔹 :=
 (-(x ≼ omega)) ⊓ ((Ord x) ⊓ (⨅ y, (Ord y) ⟹ ((- injects_into y bSet.omega) ⟹ x ⊆ᴮ y)))

@[simp]lemma aleph_one_check_exists_mem {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹] {Γ : 𝔹} : Γ ≤ exists_mem (pSet.card_ex $ aleph 1)̌   :=
begin
  simp only [show _ = pSet.card_ex (aleph ↑1), by simp],
  from check_exists_mem pSet.card_ex_aleph_exists_mem
end

@[simp]lemma B_ext_Ord : B_ext (Ord : bSet 𝔹 → 𝔹) := B_ext_inf (by simp) (by simp)

/--
The universal property of ℵ₁ is that it injects into any set which is larger than ω
-/
@[reducible]def le_of_omega_lt (x : bSet 𝔹) : 𝔹 := ⨅ z, Ord z ⟹ ((bSet.omega ≺ z) ⟹ (x ≼ z))

@[simp] lemma B_ext_le_of_omega_lt :
  B_ext (le_of_omega_lt : bSet 𝔹 → 𝔹) :=
by { delta le_of_omega_lt, simp }

end ordinals

section zorns_lemma

variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

theorem bSet_zorns_lemma' {Γ : 𝔹} : Γ  ≤ ⨅(X : bSet 𝔹), -(X =ᴮ ∅) ⟹ ((⨅y, (y ⊆ᴮ X ⊓ (⨅(w₁ : bSet 𝔹), ⨅(w₂ : bSet 𝔹),
  w₁ ∈ᴮ y ⊓ w₂ ∈ᴮ y ⟹ (w₁ ⊆ᴮ w₂ ⊔ w₂ ⊆ᴮ w₁))) ⟹ (bv_union y ∈ᴮ X)) ⟹ (⨆c, c ∈ᴮ X ⊓ (⨅z, z ∈ᴮ X ⟹ (c ⊆ᴮ z ⟹ c =ᴮ z)))) :=
begin
  bv_intro X, rw[<-curry_uncurry],
  have := core_aux_lemma2 (λ x, (-(x =ᴮ ∅) ⊓
         ⨅ (y : bSet 𝔹),
           (y ⊆ᴮ x ⊓
                ⨅ (w₁ w₂ : bSet 𝔹),
                  w₁ ∈ᴮ y ⊓ w₂ ∈ᴮ y ⟹ (w₁ ⊆ᴮ w₂ ⊔ w₂ ⊆ᴮ w₁)) ⟹
             bv_union y ∈ᴮ x)) (λ x, ⨆ (c : bSet 𝔹), c ∈ᴮ x ⊓ ⨅ (z : bSet 𝔹), z ∈ᴮ x ⟹ (c ⊆ᴮ z ⟹ c =ᴮ z))
             (by change B_ext _; simp) (by change B_ext _; simp) _ _,

  rw[eq_top_iff] at this, replace this := (le_trans le_top this : Γ ≤ _),
    from this X,
    dsimp, intros u Hu, rw[eq_top_iff] at Hu ⊢, bv_split,
    apply bSet_zorns_lemma, from (top_unique ‹_›),
    from ‹_›, apply top_unique, dsimp, apply bv_use ({∅} : bSet 𝔹),
    simp, split,
      {apply top_unique, rw[<-imp_bot], bv_imp_intro,
        rw[bv_eq_unfold] at H, bv_split,
        replace H_left := H_left none,
        dsimp at H_left, replace H_left := H_left (le_top),
        from bot_of_mem_self' ‹_›},
    intros x, refine poset_yoneda _, intros Γ a,
    simp only [le_inf_iff] at *, cases a,
    apply mem_singleton_of_eq,
    refine subset_ext (by simp) _,
    rw[subset_unfold'], bv_intro w, bv_imp_intro,
    have := bv_union_spec' x, show 𝔹, from Γ_1,
    replace this := this w, bv_split,
    replace this_left := this_left ‹_›,
    bv_cases_at this_left w',
    rw[subset_unfold'] at a_left,
    bv_split, replace a_left := a_left w' ‹_›,
    have : Γ_2 ≤ ∅ =ᴮ w', by {apply eq_of_mem_singleton, from ‹_›},
    apply bv_exfalso, apply bot_of_mem_empty, show bSet 𝔹, from w,
    bv_cc
end


end zorns_lemma

section CH

variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

local infix `≺`:75 := (λ x y, -(larger_than x y))

local infix `≼`:75 := (λ x y, injects_into x y)

def CH : 𝔹 := - ⨆ x, Ord x ⊓ ⨆y, Ord y ⊓ omega ≺ x ⊓ x ≺ y ⊓ y ≼ 𝒫 omega

def CH₂ : 𝔹 := - ⨆x, Ord x ⊓ (omega ≺ x) ⊓ (x ≺ 𝒫(omega))

end CH

end bSet
