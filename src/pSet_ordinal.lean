/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
import set_theory.ordinal set_theory.zfc tactic.tidy set_theory.cofinality .to_mathlib data.nat.enat

open ordinal

open cardinal

local prefix `#`:70 := cardinal.mk

noncomputable theory

local attribute [instance, priority 0] classical.prop_decidable

universe u

namespace ordinal

lemma lt_zero_false {x : ordinal} : x < 0 → false :=
by {apply not_lt_of_ge, from zero_le _}

end ordinal

open ordinal

namespace pSet

lemma powerset_type {x : pSet} : (powerset x).type = set (x.type) := by cases x; refl

@[simp]lemma mem.mk' {x : pSet} {i} : x.func i ∈ x :=
by {cases x; apply pSet.mem.mk}

lemma mem_unfold {x y : pSet} : x ∈ y ↔ ∃ j : y.type, equiv x (y.func j) :=
by cases y; refl

lemma mem_mem_false {x y : pSet.{u}} (H₁:  x ∈ y) (H₂ : y ∈ x) : false :=
begin
  have := Set.regularity {⟦x⟧, ⟦y⟧},
  have H_nonempty : {⟦x⟧, ⟦y⟧} ≠ ∅,
    by {have := Set.eq_empty, intro H, have := (this {⟦x⟧, ⟦y⟧}).mp H,
      specialize this ⟦x⟧, apply this, simp},
  specialize this ‹_›, rcases this with ⟨z, ⟨Hz₁, Hz₂⟩⟩,
  cases Set.mem_insert.mp Hz₁,
  rw[h] at Hz₂, have := (Set.eq_empty _).mp Hz₂, apply this,
  show Set, from ⟦x⟧, simp, exact H₁,

  have := Set.mem_singleton.mp h,
  rw[this] at Hz₂, have := (Set.eq_empty _).mp Hz₂, apply this,
  show Set, from ⟦y⟧, simp, exact H₂
end

@[simp]lemma mem_self {x : pSet.{u}} (H : x ∈ x) : false := mem_mem_false H H

@[reducible]def succ (x : pSet) : pSet := insert x x

@[simp]lemma typein_lt_type' {ξ : ordinal} {i : ξ.out.α} : @typein _ ξ.out.r ξ.out.wo i < ξ :=
by {convert @typein_lt_type _ (ξ.out.r) (ξ.out.wo) i, simp}

@[reducible]def ordinal.mk : ordinal.{u} → pSet.{u} :=
λ η, limit_rec_on η ∅ (λ ξ mk_ξ, pSet.succ mk_ξ)
  (λ ξ h_limit ih, ⟨ξ.out.α, λ i, ih (@typein _ ξ.out.r ξ.out.wo i) (by simp)⟩)

def card_ex : cardinal.{u} → pSet.{u} := λ κ, ordinal.mk (ord κ)

@[simp]lemma mk_type {α} {A} : (pSet.mk α A).type = α := rfl

@[simp]lemma mk_func {α} {A} : (pSet.mk α A).func = A := rfl

@[simp]lemma mk_func' {α} {A} {i} : (pSet.mk α A).func i = A i := rfl

lemma mk_eq {x : pSet} : x = ⟨x.type, x.func⟩ :=
by induction x; refl

@[simp]lemma eta {x : pSet} : pSet.mk x.type x.func = (x : pSet) := (@mk_eq x).symm

@[simp]lemma mk_type_forall {α} {A} {P : (pSet.mk α A).type → Prop} :
  (∀ x : (pSet.mk α A).type, P x) ↔ ∀ x : α, P x := by refl

@[simp]lemma ordinal.mk_zero : ordinal.mk 0 = ∅ :=
by simp[ordinal.mk]

@[simp]lemma ordinal.mk_zero_type : (ordinal.mk 0).type = (ulift empty) :=
begin
  simp[ordinal.mk], unfold has_emptyc.emptyc pSet.empty, refl
end

def ordinal.mk_zero_cast : ulift empty → (ordinal.mk 0).type  :=
  cast (ordinal.mk_zero_type.symm)

def ordinal.mk_zero_cast' : (ordinal.mk 0).type → ulift empty :=
  cast (ordinal.mk_zero_type)

@[simp]lemma ordinal.mk_zero_forall {P : (ordinal.mk 0).type → (ordinal.mk 0).type → Prop} : ∀ i j : (ordinal.mk 0).type, P i j ↔ ∀ i' j' : (ulift empty), P (ordinal.mk_zero_cast i') (ordinal.mk_zero_cast j') :=
by {tidy, have := ordinal.mk_zero_cast' i, repeat{cases this}}

@[simp]lemma ordinal.mk_succ {η : ordinal} : ordinal.mk (ordinal.succ η) = pSet.succ (ordinal.mk η) :=
by {simp[ordinal.mk]}

@[simp]lemma succ_type {x : pSet} : (succ x).type = option (x.type) :=
by {induction x, refl}

@[simp]lemma option_succ_type {x : pSet} : option (succ x).type = option (option (x.type)) :=
by simp

def succ_type_cast {x : pSet} : (succ x).type → option(x.type) := cast succ_type
def succ_type_cast' {x : pSet} : option(x.type) → (succ x).type  := cast succ_type.symm

def option_cast' {x : pSet} :  option (option x.type) → option (succ x).type :=
cast option_succ_type.symm

@[simp]lemma succ_func_none {x : pSet} : (succ x).func (succ_type_cast' none) = x :=
by induction x; refl

@[simp]lemma succ_func_some {x : pSet} {i} : (succ x).func (succ_type_cast' (some i)) = x.func (i) :=
by induction x; refl

lemma succ_type_forall {x : pSet} {P : (succ x).type → Prop} :
  (∀ (i : (succ x).type), P i) = ∀ (i : option (x.type)), P (succ_type_cast' i) :=
by {cases x, refl}

lemma succ_type_exists {x : pSet} {P : (succ x).type → Prop} :
  (∃ (i : (succ x).type), P i) = ∃ (i : option (x.type)), P (succ_type_cast' i) :=
by {cases x, refl}

lemma option_succ_type_forall {x : pSet} {P : option (succ x).type → Prop} :
  (∀ i : option (succ x).type, P i) = ∀ (i : option (option x.type)), P (option_cast' i) :=
by {cases x, refl}

@[simp]lemma ordinal.mk_limit {η : ordinal} (H_limit : is_limit η) : ordinal.mk η = ⟨η.out.α, λ x, ordinal.mk (@typein _ (η.out.r) (η.out.wo) x)⟩ :=
by simp[*, ordinal.mk]

@[simp]lemma ordinal.mk_limit_type {η : ordinal} (H_limit : is_limit η) : (ordinal.mk η).type = η.out.α :=
by simp*; refl

@[simp]lemma mem_mk_limit_of_lt {η : ordinal} (H_limit : is_limit η) (ξ : ordinal) (Hξ : ξ < η) : ordinal.mk ξ ∈ ordinal.mk η :=
begin
  conv {to_rhs, rw[ordinal.mk_limit ‹_›]},
  convert mem.mk ((λ (x : (quotient.out η).α), ordinal.mk (typein ((quotient.out η).r) x))) _,
  swap, exact enum η.out.r ξ (by convert Hξ; simp), simp
end

def epsilon_well_orders (x : pSet.{u}) : Prop :=
  (∀ y, y ∈ x → (∀ z, z ∈ x → (equiv y z ∨ y ∈ z ∨ z ∈ y))) ∧
  (∀ u, u ⊆ x → (¬ (equiv u (∅ : pSet.{u})) → ∃ y, (y ∈ u ∧ (∀ z', z' ∈ u → ¬ z' ∈ y))))

def is_transitive (x : pSet) : Prop := ∀ y, y ∈ x → y ⊆ x

def Ord (x : pSet) : Prop := epsilon_well_orders x ∧ is_transitive x

@[simp]lemma is_transitive_of_Ord {x} (H : Ord x) : is_transitive x := H.right

@[simp]lemma is_ewo_of_Ord {x} (H : Ord x) : epsilon_well_orders x := H.left

lemma equiv_of_eq {x y : pSet} : ⟦x⟧ = ⟦y⟧ → pSet.equiv x y :=
λ H, quotient.eq.mp H

lemma equiv_iff_eq {x y : pSet} : equiv x y ↔ ⟦x⟧ = ⟦y⟧ :=
⟨λ _, quotient.sound ‹_›, λ _, quotient.eq.mp ‹_›⟩

instance mem_of_pSet : has_mem (quotient pSet.setoid) (quotient pSet.setoid) :=
{mem := Set.mem}

lemma mem_iff {x y : pSet} : x ∈ y ↔ ⟦x⟧ ∈ ⟦y⟧ := by refl

lemma mem_insert {x y z : pSet} (H : x ∈ insert y z) : equiv x y ∨ x ∈ z :=
begin
  have this₁ : ⟦x⟧ ∈ Set.insert ⟦y⟧ ⟦z⟧, by assumption,
  have := Set.mem_insert.mp, unfold insert has_insert.insert at this,
  specialize this this₁, cases this,
  from or.inl (equiv_of_eq ‹_›), from or.inr ‹_›
end

lemma mem_insert' {x y z : pSet} (H : equiv x y ∨ x ∈ z) : x ∈ insert y z :=
begin
  change ⟦x⟧ ∈ Set.insert ⟦y⟧ ⟦z⟧,
  have := Set.mem_insert.mpr, unfold insert has_insert.insert at this,
  apply this, cases H, from or.inl (quotient.sound ‹_›), from or.inr H
end

@[simp]lemma mem_succ (x : pSet) : x ∈ succ x :=
  by {apply mem_insert', left, apply equiv.refl}

lemma subset_of_all_mem {x y : pSet} (H : ∀ z, z ∈ y → z ∈ x) : y ⊆ x :=
begin
  cases x, cases y, unfold has_subset.subset pSet.subset,
  intro a, exact H (y_A a) (mem.mk y_A a)
end

lemma all_mem_of_subset {x y : pSet} (H : y ⊆ x) : ∀ z, z ∈ y → z ∈ x :=
begin
  intros z Hz, cases y, cases x, unfold has_subset.subset pSet.subset at H,
  cases Hz with b Hb,
  specialize H b, cases H with b' Hb', use b',
  apply equiv.trans Hb ‹_›
end

lemma subset_iff_all_mem {x y : pSet} : y ⊆ x ↔ ∀ z, z ∈ y → z ∈ x :=
by {split; intros; [apply all_mem_of_subset, apply subset_of_all_mem], repeat{assumption}}

lemma Set.subset_iff_all_mem {x y : Set} : y ⊆ x ↔ ∀ z, z ∈ y → z ∈ x :=
by refl

@[simp]lemma Set.mem.mk' {x : pSet} {i} : ⟦x.func i⟧ ∈ ⟦x⟧ :=
by {rw[<-mem_iff], exact mem.mk'}

lemma mem_trans_of_transitive {x y z : pSet} (H₁ : x ∈ y) (H₂ : y ∈ z) (H_trans : is_transitive z) : x ∈ z :=
subset_iff_all_mem.mp (H_trans y H₂) x H₁

lemma empty_empty : (∅ : Set) = ⟦(∅ : pSet)⟧ := by refl

lemma exists_mem_of_nonempty {x : pSet.{u}} (H : ¬ equiv x (∅ : pSet.{u})) : ∃ y, y ∈ x :=
begin
  have := (Set.eq_empty ⟦x⟧).mpr, by_contra,
  simp at a, have this' : ∀ (x' : Set), x' ∉ ⟦x⟧,
    by {intro x', specialize a x'.out, intro H, apply a,
    change ⟦quotient.out x'⟧ ∈ ⟦x⟧, rwa[quotient.out_eq x']},
  apply H, apply @equiv_of_eq x ∅, solve_by_elim
end

lemma not_empty_of_not_equiv_empty {x : pSet.{u}} (H : ¬ equiv x (∅ : pSet.{u})) : ⟦x⟧ ≠ (∅ : Set) :=
by {intro H', apply H, from equiv_of_eq H'}

@[simp]lemma Ord_empty : Ord (∅ : pSet.{u}) :=
begin
  unfold has_emptyc.emptyc pSet.empty,
  unfold Ord epsilon_well_orders is_transitive, split,
  swap, {tidy}, split, {tidy},
  intros u H₁ H₂,  exfalso, apply H₂,
  apply mem.ext, intro w; split; intro H,
  swap, cases H, repeat{cases H_w},
  cases u, unfold has_mem.mem mem at H, cases H with w' Hw',
  specialize H₁ w', cases H₁ with b _, repeat{cases b}
end

lemma well_founded (u : pSet.{u}) (H_nonempty : ¬equiv u (∅ : pSet.{u})) : ∃ (y : pSet), y ∈ u ∧ ∀ (z' : pSet), z' ∈ u → z' ∉ y :=
begin
  have := Set.regularity ⟦u⟧ (not_empty_of_not_equiv_empty ‹_›),
  rcases this with ⟨y, ⟨H₁, H₂⟩⟩, use y.out, rw[<-quotient.out_eq y] at H₁,
  refine ⟨H₁, _⟩, intros z' Hz' Hz'',
  have Hz'2 : ⟦z'⟧ ∈ ⟦u⟧ := ‹_›,
  have Hz''2 : ⟦z'⟧ ∈ y := by {change ⟦z'⟧ ∈ ⟦quotient.out y⟧ at Hz'', rw[quotient.out_eq] at Hz'', from ‹_›},
  have := (@Set.mem_inter ⟦u⟧ y ⟦z'⟧).mpr (and.intro ‹_› ‹_›),
  apply Set.mem_empty ⟦z'⟧, apply (mem.congr_right _).mp,
  rw[mem_iff],  show pSet,
  refine quotient.out (_), change Set, exact ⟦u⟧ ∩ y,
  simp, change ⟦z'⟧ ∈ ⟦_⟧, rw[quotient.out_eq], exact this,
  apply equiv_of_eq, simp, change ⟦_⟧ = ⟦_⟧,
  rw[quotient.out_eq], exact ‹_›
end

lemma transitive_succ (x : pSet) (H : is_transitive x) : is_transitive (succ x) :=
begin
  intros y Hy, have := mem_insert Hy,
     cases this, apply subset_of_all_mem, intros z H, unfold succ, apply mem_insert',
     right, have := mem.congr_right this, apply this.mp H, apply subset_of_all_mem,
     intros z Hz, apply mem_insert', right, have := H y ‹_›,
     have := all_mem_of_subset this, from this z Hz,
end

@[simp]lemma Ord_succ (x : pSet) (H : Ord x) : Ord (succ x) :=
begin
  refine ⟨_,_⟩, show is_transitive _,
    {apply transitive_succ _ H.right},
    {split,
      {intros y Hy z Hz, have this₁ := mem_insert Hy, have this₂ := mem_insert Hz,
       cases this₁, cases this₂, left, {[smt] eblast_using [equiv.trans, equiv.symm]},
       right, right, have := (mem.congr_right this₁).mpr, solve_by_elim,
       cases this₂, have := (mem.congr_right this₂).mpr, right, left, solve_by_elim,
       exact H.left.left y ‹_› z ‹_›},
      {intros u Hu H_nonempty,
         replace H := H.left.right u,
         replace Hu := all_mem_of_subset Hu,
         apply well_founded, from ‹_›}},
end

lemma mk_mem_mk_of_lt {ξ η : ordinal} (H_lt : ξ < η) : (ordinal.mk ξ) ∈ (ordinal.mk η) :=
begin
  revert H_lt, revert ξ, apply limit_rec_on η; clear η,
    { intros, exfalso, from lt_zero_false ‹_› },
    { intros η ih ξ H_lt, replace H_lt := ordinal.lt_succ.mp ‹_›,
      by_cases ξ = η,
        { subst h, simp },
        { suffices H_lt_η : ξ < η,
            by {simp, from mem_insert' (or.inr (by solve_by_elim))},
           from lt_of_le_of_ne ‹_› ‹_› }},
    { intros η H_limit ih ξ H_lt, from mem_mk_limit_of_lt ‹_› _ ‹_› }
end

lemma ordinal.lt_of_mk_mem {ξ η : ordinal} (H_lt : ordinal.mk ξ ∈ ordinal.mk η) : ξ < η :=
begin
  have := lt_trichotomy ξ η, repeat{cases this},
    { from ‹_› },
    { exfalso, from mem_self ‹_› },
    { suffices : ordinal.mk η ∈ ordinal.mk ξ,
        by {exfalso, from mem_mem_false ‹_› ‹_›}, 
      from mk_mem_mk_of_lt ‹_› }
end

lemma transitive_Union (x : pSet) (H : ∀ y ∈ x, is_transitive y) : is_transitive (Union x) :=
begin
  intros z Hz, apply subset_of_all_mem, intros w Hw,
  rw[mem_Union] at Hz, rcases Hz with ⟨y, ⟨Hy, Hy'⟩⟩,
  have H_trans := H y ‹_› z ‹_›, have := all_mem_of_subset ‹_› w ‹_›,
  apply mem_Union.mpr, use y, use ‹_›, from ‹_›
end

lemma equiv_mk_of_mem_mk {η : ordinal} : ∀ x, x ∈ (ordinal.mk η) → ∃ ρ < η, equiv x $ ordinal.mk ρ :=
begin
  apply limit_rec_on η; clear η,
    { intros x H, exfalso, simpa[pSet.mem_empty] using H },
    { intros η ih ξ H_mem, rw[ordinal.mk_succ] at H_mem,
      replace H_mem := mem_insert H_mem,
      cases H_mem,
        { use η, from ⟨(lt_succ_self _), ‹_›⟩},
        { rcases ih _ ‹_› with ⟨p, H₁, H₂⟩,
          use p, use lt_trans ‹_› (lt_succ_self _), from ‹_›}},
    { intros η H_limit ih x Hx, rw[ordinal.mk_limit ‹_›] at Hx,
      cases Hx with i H_i, dsimp at H_i, use (typein ((quotient.out η).r) i),
      finish }
end

lemma Ord_limit : ∀ (o : ordinal), is_limit o → (∀ (o' : ordinal), o' < o → Ord (ordinal.mk o')) → Ord (ordinal.mk o) :=
begin
  intros η Hη ih, 
  refine ⟨_,_⟩,
    { unfold epsilon_well_orders, refine ⟨_,_⟩,
        { intros x Hx z Hz, have this₁ := equiv_mk_of_mem_mk _ Hx,
          have this₂ := equiv_mk_of_mem_mk _ Hz,
          rcases this₁ with ⟨ξ₁, H₁, H₂⟩,
          rcases this₂ with ⟨ξ₂, H₁', H₂'⟩,
          have := lt_trichotomy ξ₁ ξ₂, repeat{cases this},
          right, left, rw[mem.congr_left H₂], rw[mem.congr_right H₂'],
          from mk_mem_mk_of_lt ‹_›,
          left, from equiv.trans H₂ (equiv.symm H₂'),
          right, right, rw[mem.congr_right H₂], rw[mem.congr_left H₂'],
          from mk_mem_mk_of_lt ‹_›},
        { exact λ _ _ _, well_founded _ ‹_› },
        },
    { rw[ordinal.mk_limit Hη],
      intros y Hy, cases Hy with y_ξ Hy_ξ, rw[subset.congr_left Hy_ξ],
      let ξ := typein ((quotient.out η).r) y_ξ,
      change ordinal.mk ξ ⊆ _,
      have ξ_lt_η : ξ < η,
        by {simp[typein_lt_type]},
      have : ∀ x, x ∈ (ordinal.mk ξ) → ∃ ρ < ξ, equiv x $ ordinal.mk ρ,
        by {apply equiv_mk_of_mem_mk},
      apply subset_of_all_mem, intros z Hz,
      specialize this z Hz, rcases this with ⟨ρ, Hρ₁, Hρ₂⟩,
      rw[mem.congr_left Hρ₂],
      convert (mem_mk_limit_of_lt ‹_› _ (lt_trans Hρ₁ ‹_›)), simp* } 
end

@[simp]lemma Ord_mk (η : ordinal) : Ord (ordinal.mk η) :=
begin
  apply limit_rec_on η,
    { simp },
    { intros; simp* },
    { exact Ord_limit }
end

-- lemma transitive_mk (η : ordinal.{u}) : is_transitive $ ordinal.mk η :=
-- begin
--   apply limit_rec_on η,
--     simp[Ord_empty.right],
--     intros ξ ih,
--   simp, from transitive_succ _ ‹_›,
--   intros ξ h_limit ih,

--   simp*, intros y yH, sorry
-- end

lemma mem_mem_mem_false {x y z : pSet.{u}} (H₁ : x ∈ y) (H₂ : y ∈ z) (H₃ : z ∈ x) : false :=
begin
  have := Set.regularity {⟦x⟧,⟦y⟧,⟦z⟧},
  have H_nonempty : {⟦x⟧, ⟦y⟧, ⟦z⟧} ≠ ∅,
    by {have := Set.eq_empty, intro H, have := (this {⟦x⟧,⟦y⟧,⟦z⟧}).mp H, specialize this ⟦x⟧,
    apply this, simp, apply (Set.mem_insert).mpr, right, simp},

  specialize this ‹_›, rcases this with ⟨w, ⟨Hw₁, Hw₂⟩⟩,
  cases Set.mem_insert.mp Hw₁, rw[h] at Hw₂, have := (Set.eq_empty _).mp Hw₂, apply this,
  show Set, from ⟦y⟧, simp, refine ⟨_,‹_›⟩, apply (Set.mem_insert).mpr, right, simp,

  replace h := Set.mem_insert.mp h, cases h,
  rw[h] at Hw₂, have := (Set.eq_empty _).mp Hw₂, apply this,
  show Set, from ⟦x⟧, simp, refine ⟨_,‹_›⟩, apply (Set.mem_insert).mpr, right, simp,

    replace h := Set.mem_insert.mp h, cases h,
  rw[h] at Hw₂, have := (Set.eq_empty _).mp Hw₂, apply this,
  show Set, from ⟦z⟧, simp, refine ⟨_,‹_›⟩, apply (Set.mem_insert).mpr, left, simp,
  apply mem_empty w.out, rw[<-quotient.out_eq w] at h, exact h
end

def mem_witness {y w : pSet.{u}} (H : w ∈ y) : Σ'(y_a : y.type), (equiv w (y.func y_a)) :=
begin
  cases y, unfold has_mem.mem pSet.mem at H, have := classical.indefinite_description _ H,
  cases this with a Ha, use a, from ‹_›
end

lemma transitive_of_mem_Ord (y x : pSet.{u}) (H : Ord x) (H_mem : y ∈ x) : is_transitive y :=
begin
  intros w Hw, apply subset_of_all_mem, intros z Hz,

  cases H with H_left H_trans, cases H_left with H_tri H_wf, unfold is_transitive at H_trans,
  have H_w_in_x : w ∈ x,
    by {specialize H_trans y ‹_›, rw[subset_iff_all_mem] at H_trans, specialize H_trans w ‹_›,
    exact H_trans},
  have H_z_in_x : z ∈ x,
    by {specialize H_trans w ‹_›, rw[subset_iff_all_mem] at H_trans, from H_trans z ‹_›},
  by_contra,
    specialize H_tri y ‹_› z ‹_›, simp* at H_tri,
    cases H_tri,
  have H_bad : w ∈ z,
    by {apply (mem.congr_right _).mp, from Hw, from ‹_›},
   apply mem_mem_false H_bad ‹_›,
   apply mem_mem_mem_false H_tri Hz ‹_›
end

lemma mk_equiv_of_eq {β₁ β₂ : ordinal.{u}} (H : β₁ = β₂) : equiv (ordinal.mk β₁) (ordinal.mk β₂) :=
by rw[H]; apply equiv.refl

lemma mk_mem_succ {η : ordinal.{u}} : ordinal.mk η ∈ ordinal.mk (ordinal.succ η) :=
by simp

lemma subset_Union {x y : pSet.{u}} (H : y ∈ x) : y ⊆ Union x :=
begin
  apply subset_of_all_mem, intros z Hz, apply mem_Union.mpr,
  use y, from ⟨‹_›,‹_›⟩
end


-- WARNING: pSet.is_func is the same as bSet.is_function, not bSet.is_func

--f ⊆ prod x y ∧ ∀z:Set.{u}, z ∈ x → ∃! w, pair z w ∈ f
@[reducible]def is_func (x y f : pSet.{u}) : Prop := Set.is_func ⟦x⟧ ⟦y⟧ ⟦f⟧


@[reducible]def is_weak_func (x y f : pSet.{u}) : Prop :=
  (∀ z, z ∈ ⟦x⟧ →  ∃! w, w ∈ ⟦y⟧ ∧ Set.pair z w ∈ ⟦f⟧)

@[reducible]def is_extensional (f : pSet.{u}) : Prop := ∀ w₁ w₂ v₁ v₂, Set.pair ⟦w₁⟧ ⟦v₁⟧ ∈ ⟦f⟧ → Set.pair ⟦w₂⟧ ⟦v₂⟧ ∈ ⟦f⟧ → (equiv w₁ w₂) → (equiv v₁ v₂)

@[reducible]def is_surj (x y f : pSet.{u}) : Prop := ∀ b : pSet.{u}, b ∈ y → ( ∃ a : pSet.{u}, a ∈ x ∧ (Set.pair ⟦a⟧ ⟦b⟧ ∈ ⟦f⟧))

-- lemma mk_lt_of_lt {β₁ β₂ : ordinal.{u}} (H : β₁ < β₂) : ordinal.mk β₁ ∈ ordinal.mk β₂ :=
-- begin
--   revert H, revert β₁, apply limit_rec_on β₂,
--   intros β₁ H, exfalso, sorry, -- there is no principal segment in 0

--   intro η, intro ih,
--   intros ξ h_ξ,

--   {haveI po_ord : partial_order ordinal.{u} := by apply_instance,
--   have : ξ ≤ η, from ordinal.lt_succ.mp ‹_›,
--   have this' := (@le_iff_lt_or_eq ordinal _ ξ η).mp ‹_›,
--   cases this',
--     {have this'' := @ih ξ ‹_›,
--       suffices H : is_transitive (ordinal.mk (ordinal.succ η)),
--       specialize H (ordinal.mk η) (by simp), rw[subset_iff_all_mem] at H,
--       from H (ordinal.mk ξ) ‹_›, apply transitive_mk},
--     {rw[this'], simp}},

--   intros η h_limit ih ξ hξ, simp only [h_limit, ordinal.mk_limit], sorry
--   -- apply mem_Union.mpr, use (ordinal.mk (ordinal.succ ξ)), split,
--   -- swap, simp, split, swap, -- to finish this, need a lemma which says that given a (ξ + 1) which is less than η, there exists an isomorphic initial segment in (quotient.out η)
--   -- sorry, sorry
-- end

-- lemma mk_trichotomy (β₁ β₂ : ordinal.{u}) : (equiv (ordinal.mk β₁) (ordinal.mk β₂)) ∨ (ordinal.mk β₁) ∈ (ordinal.mk β₂) ∨ (ordinal.mk β₂) ∈ (ordinal.mk β₁) :=
-- begin
--   have := lt_trichotomy β₁ β₂,
--   repeat{cases this},
--     right,left, from mk_lt_of_lt ‹_›,
--     left, apply equiv.refl,
--     right,right, from mk_lt_of_lt ‹_›
-- end

private lemma ordinal.mk_inj_successor : ∀ (o : ordinal.{u}), (∀ (i j : type (ordinal.mk o)), i ≠ j →
  ¬equiv (func (ordinal.mk o) i) (func (ordinal.mk o) j)) →
  ∀ (i j : type (ordinal.mk (ordinal.succ o))), i ≠ j →
  ¬equiv (func (ordinal.mk (ordinal.succ o)) i) (func (ordinal.mk (ordinal.succ o)) j) :=
begin
  intros ξ ih, rw[ordinal.mk_succ], rw[succ_type_forall], intro i, rw[succ_type_forall],
  intros j H_neq, cases i; cases j,
   {exfalso, from H_neq rfl},
   {simp only [pSet.succ_func_none, pSet.succ_func_some],
     intro H, have : (func (ordinal.mk ξ) j) ∈ (ordinal.mk ξ),
     by {cases (ordinal.mk ξ), apply mem.mk}, suffices : (ordinal.mk ξ) ∈ (ordinal.mk ξ),
     from mem_self ‹_›, from (mem.congr_left ‹_›).mpr ‹_›},
   {simp only [pSet.succ_func_none, pSet.succ_func_some],
     intro H, have : (func (ordinal.mk ξ) i) ∈ (ordinal.mk ξ),
     by {cases (ordinal.mk ξ), apply mem.mk}, suffices : (ordinal.mk ξ) ∈ (ordinal.mk ξ),
     from mem_self ‹_›, from (mem.congr_left ‹_›).mp ‹_›},
   {have : i ≠ j, from λ _, by apply H_neq; simp*, simp*}
end

theorem zero_eq_type_empty' : (0 : ordinal.{u}) = ordinal.lift (@ordinal.type empty empty_relation _) :=
begin
  apply quotient.sound, split,
  from { to_fun := by tidy,
  inv_fun := by tidy,
  left_inv := dec_trivial,
  right_inv := dec_trivial,
  ord := dec_trivial}
end

lemma ordinal.mk_coherent {ξ β : ordinal} {H_lt : β < ξ} :
  ∃ j : (ordinal.mk ξ).type, (ordinal.mk ξ).func j = ordinal.mk β :=
begin
  revert β H_lt, apply well_founded.induction wf ξ,
  intros β, apply limit_rec_on β,
  {intros _ _ _, exfalso, from lt_zero_false ‹_›},
  intros η ih₁ ih₂ δ h_δ, replace h_δ := ordinal.lt_succ.mp h_δ,
  by_cases δ = η,
    rw[ordinal.mk_succ], rw[succ_type_exists],
    use none, simp[h],
  have : δ < η, by {have := lt_trichotomy δ η, finish},
  rw[ordinal.mk_succ,succ_type_exists],
  have := ih₂ η (by apply ordinal.lt_succ_self), show ordinal, from δ,
  cases this with i_δ i_δ_spec, use (some i_δ), simp[i_δ_spec], from ‹_›,
  intros η h_limit ih₁ ih₂ δ h_δ, rw[ordinal.mk_limit ‹_›], simp,
  use @enum _ η.out.r η.out.wo δ (by {convert h_δ, simp}), simp
end

private lemma ordinal.mk_inj_limit : ∀ (o : ordinal.{u}), is_limit o → (∀ (o' : ordinal),
  o' < o → ∀ (i j : type (ordinal.mk o')), i ≠ j →
    ¬equiv (func (ordinal.mk o') i) (func (ordinal.mk o') j)) →
      ∀ (i j : type (ordinal.mk o)), i ≠ j →
        ¬equiv (func (ordinal.mk o) i) (func (ordinal.mk o) j) :=
begin
  intros ξ h_limit ih, rw[ordinal.mk_limit ‹_›],
  rw[mk_type_forall], intro i, rw[mk_type_forall], intros j H_neq,
  simp only [mk_func],
  let i' := @typein ξ.out.α ((quotient.out ξ).r) ξ.out.wo i,
  let j' := @typein ξ.out.α ((quotient.out ξ).r) ξ.out.wo j,
  have := (lt_trichotomy i' j'), cases this, swap, cases this,
    {suffices : i = j, by contradiction, from ((@typein_inj _ ξ.out.r ξ.out.wo) i j).mp ‹_›},
    {specialize ih (ordinal.succ i') (by {have := (@succ_lt_of_is_limit ξ ‹_› i').mpr
      (by {dsimp[i'], convert @typein_lt_type _ ξ.out.r ξ.out.wo i, simp}), from ‹_›}),
      rw[ordinal.mk_succ, succ_type_forall] at ih,
      specialize ih none, rw[succ_type_forall] at ih,
      have := @ordinal.mk_coherent i' j' this,
      cases this with j'' j''_spec,
     specialize ih (some j'')
     (by {intro H, suffices : none = (some j''),
     by contradiction, unfold succ_type_cast' at H, cc}),
     convert ih using 2, simp, simp*},
    {specialize ih (ordinal.succ j') (by {have := (@succ_lt_of_is_limit ξ ‹_› j').mpr
      (by {dsimp[j'], convert @typein_lt_type _ ξ.out.r ξ.out.wo j, simp}), from ‹_›}),
      rw[ordinal.mk_succ, succ_type_forall] at ih,
      specialize ih none, rw[succ_type_forall] at ih,
      have := @ordinal.mk_coherent j' i' this,
      cases this with i'' i''_spec,
     specialize ih (some i'')
     (by {intro H, suffices : none = (some i''),
     by contradiction, unfold succ_type_cast' at H, cc}),
     intro H, replace H := equiv.symm H, revert H, change ¬ _,
     convert ih using 2, simp, simp*}
end

lemma ordinal.mk_inj (η : ordinal.{u}) : ∀ (i j : ((ordinal.mk η).type : Type u))
  (H_neq : i ≠ j), ¬ equiv ((ordinal.mk η).func i) ((ordinal.mk η).func j) :=
begin
  apply limit_rec_on η,
    {rw[ordinal.mk_zero], intro i, repeat{cases i}},
    {from ordinal.mk_inj_successor},
    {from ordinal.mk_inj_limit}
end

lemma eq_of_mk_equiv {η₁ η₂ : ordinal} (H_equiv : equiv (ordinal.mk η₁) (ordinal.mk η₂)) : η₁ = η₂ :=
begin
  refine le_antisymm _ _,
    { rw[<-not_lt], intro H_lt, replace H_lt := mk_mem_mk_of_lt H_lt,
      suffices this : ordinal.mk η₁ ∈ ordinal.mk η₁,
        by {exact mem_self ‹_›},
      rwa[<-mem.congr_left H_equiv] at H_lt},
    { rw[<-not_lt], intro H_lt, replace H_lt := mk_mem_mk_of_lt H_lt,
      suffices this : ordinal.mk η₂ ∈ ordinal.mk η₂,
        by {exact mem_self ‹_›},
      rwa[mem.congr_left H_equiv] at H_lt}
end

lemma eq_iff_mk_eq {η₁ η₂ : ordinal} : η₁ = η₂ ↔ equiv (ordinal.mk η₁) (ordinal.mk η₂) :=
⟨λ _, mk_equiv_of_eq ‹_›, λ _, eq_of_mk_equiv ‹_›⟩

lemma mk_type_mk_eq (κ : cardinal) (H_inf : cardinal.omega ≤ κ) : #(ordinal.mk (ord κ)).type = κ :=
begin
  cases (@exists_aleph κ).mp ‹_› with k H_k,
  subst H_k, rw[ordinal.mk_limit_type (aleph_is_limit (k))], convert card_ord (aleph k),
  rw[<-(@card_type _ (aleph k).ord.out.r (aleph k).ord.out.wo)], simp
end

@[simp]lemma mk_type_mk_eq' (κ : cardinal) (H_inf : cardinal.omega < κ) : #(ordinal.mk (ord κ)).type = κ :=
mk_type_mk_eq _ (le_of_lt ‹_›)

@[simp]lemma mk_type_mk_eq'' {κ : cardinal} {H_inf : cardinal.omega ≤ κ} : #(card_ex κ).type = κ :=
mk_type_mk_eq κ ‹_›

@[simp]lemma mk_type_mk_eq''' {κ : cardinal} {H_inf : cardinal.omega < κ} : #(card_ex κ).type = κ :=
mk_type_mk_eq _ (le_of_lt ‹_›)

@[simp]lemma mk_type_mk_eq'''' {k} : #(ordinal.mk (aleph k).ord).type = (aleph k) :=
begin
  rw[ordinal.mk_limit_type (aleph_is_limit (k))], convert card_ord (aleph k),
  rw[<-(@card_type _ (aleph k).ord.out.r (aleph k).ord.out.wo)], simp
end

lemma zero_aleph : cardinal.omega = (aleph 0) := by simp

@[simp]lemma mk_type_omega_eq : #(ordinal.mk (cardinal.omega).ord).type = cardinal.omega :=
mk_type_mk_eq _ (by refl)

@[simp]lemma mk_omega_eq_mk_omega : #(pSet.type omega) = cardinal.omega :=
begin
  apply quotient.sound,
  from ⟨{ to_fun := id,
  inv_fun := id,
  left_inv := λ _, rfl,
  right_inv := λ _, rfl}⟩
end

lemma two_eq_succ_one : (2 : ordinal) = (ordinal.succ 1) :=
by {rw[succ_eq_add_one], refl}

lemma add_one_lt_add_one {a b : ordinal} : a < b ↔ (a+1) < (b+1) :=
by {repeat{rw[<-succ_eq_add_one]}, simp[succ_lt_succ]}

lemma one_lt_two : (1 : ordinal) < 2 :=
by {rw[two_eq_succ_one], from ordinal.lt_succ_self _}

lemma aleph_two_eq_succ_aleph_one : (aleph 2) = (cardinal.succ (aleph 1)) :=
by rw[<-aleph_succ]; congr

lemma aleph_one_eq_succ_aleph_zero : (aleph 1) = (cardinal.succ cardinal.omega) :=
by {rw[<-aleph_zero, <-aleph_succ], congr, simp}

lemma is_regular_aleph_one : is_regular (aleph 1) :=
by {rw[aleph_one_eq_succ_aleph_zero]; apply succ_is_regular,refl}

lemma is_regular_aleph_two : is_regular (aleph 2) :=
by {rw[aleph_two_eq_succ_aleph_one]; apply succ_is_regular; apply omega_le_aleph}

@[simp]lemma omega_lt_aleph_one : cardinal.omega < (aleph 1) :=
by {rw[<-aleph_zero], apply cardinal.aleph_lt.mpr, from zero_lt_one}

@[simp]lemma aleph_one_lt_aleph_two : aleph 1 < aleph 2 :=
by {apply cardinal.aleph_lt.mpr, from one_lt_two}

@[simp]lemma omega_lt_aleph_two : cardinal.omega < (aleph 2) :=
lt_trans (omega_lt_aleph_one) (by simp)

lemma subset_refl {x : pSet} : x ⊆ x :=
by {apply subset_of_all_mem, from λ _ _, by assumption}

lemma subset_trans {x y z : pSet} : x ⊆ y → y ⊆ z → x ⊆ z :=
by {simp only [subset_iff_all_mem], tidy}

lemma of_nat_succ {k} : of_nat (k + 1) = pSet.succ (of_nat k) :=
by unfold of_nat; tidy

lemma subset_of_le {k₁ k₂ : ℕ} (H : k₁ ≤ k₂) : of_nat k₁ ⊆ of_nat k₂ :=
begin
  induction k₂ with k₂ ih, replace H := nat.eq_zero_of_le_zero H, rw[H], unfold of_nat,
  from @subset_refl ∅,
  by_cases k₁ = (k₂ + 1),
  rw[h], apply subset_refl,
  have := nat.le_of_lt_succ (nat.lt_of_le_and_ne ‹_› ‹_›),
  suffices : of_nat k₁ ⊆ of_nat k₂,
    by {apply subset_trans this, unfold of_nat, apply subset_of_all_mem, intros w Hw,
        from mem_insert' (or.inr ‹_›)},
  from ih ‹_›
end

lemma false_of_subset_of_nat_ge {k₁ k₂ : ℕ} (H : k₁ < k₂) : ¬ (of_nat k₂ ⊆ of_nat k₁) :=
begin
  intro H, suffices : (of_nat k₁) ∈ of_nat k₁, from mem_self ‹_›,
  suffices : of_nat (k₁ + 1) ⊆ of_nat k₂,
    by {have := subset_trans this H, apply all_mem_of_subset this, apply mem_insert',
    left, from equiv.refl _},
  from subset_of_le (nat.succ_le_of_lt ‹_›)
end

lemma le_of_subset {k₁ k₂ : ℕ} (H : of_nat k₁ ⊆ of_nat k₂) : k₁ ≤ k₂ :=
by {by_contra, simp at a, replace a := false_of_subset_of_nat_ge a, contradiction}

lemma of_nat_of_mem_of_nat {y : pSet.{u}} {k} (H_mem : y ∈ (of_nat k : pSet.{u})) :
  ∃ j, equiv (y : pSet.{u}) (of_nat j : pSet.{u}) :=
begin
  induction k with k ih, {tidy},
  unfold of_nat at H_mem, cases mem_insert H_mem,
  from ⟨k, h⟩, back_chaining
end

lemma of_nat_is_transitive {k : ℕ} : is_transitive (of_nat k) :=
begin
  intros y Hy, induction k, unfold of_nat at Hy, {tidy},
  unfold of_nat at Hy, cases mem_insert ‹_›,
  apply subset_of_all_mem, intros z Hz, rw[mem.congr_right h] at Hz,
  apply (all_mem_of_subset (subset_of_le _)), from Hz, apply nat.le_succ,
  rw[subset_iff_all_mem] at k_ih ⊢, intros z Hz, specialize k_ih ‹_› z ‹_›,
  apply (all_mem_of_subset (subset_of_le (nat.le_succ _))), from ‹_›
end

lemma of_nat_mem_of_lt {k₁ k₂ : ℕ} (H_lt : k₁ < k₂) : (of_nat k₁ : pSet.{u}) ∈ (of_nat k₂ : pSet.{u}) :=
begin
  induction k₂ with k₂ ih₂, cases H_lt,
  by_cases k₁ = k₂, subst h, simp[of_nat_succ],
  have : k₁ < k₂, by {exact array.push_back_idx H_lt h},
  specialize ih₂ this, have : of_nat k₂ ∈ of_nat (nat.succ k₂),
  by simp[of_nat_succ], have this₁ := all_mem_of_subset (subset_of_le (le_of_lt ‹_›)),
  have this₂ := all_mem_of_subset (subset_of_le (le_of_lt $ lt_add_one k₂)),
  back_chaining
end

lemma lt_of_of_nat_mem {k₁ k₂ : ℕ} (H_mem : of_nat k₁ ∈ of_nat k₂) : k₁ < k₂ :=
begin
  by_contra, replace a := not_lt.mp a, have : of_nat k₂ ⊆ of_nat k₁, by apply subset_of_le ‹_›,
  rw[subset_iff_all_mem] at this, suffices : of_nat k₁ ∈ of_nat k₁, from mem_self ‹_›,
  back_chaining
end

lemma is_transitive_omega : is_transitive (omega : pSet.{u}) :=
begin
  intros z H, cases H, cases H_w with k, simp at H_h,
  rw[subset.congr_left H_h], unfold omega, rw[subset_iff_all_mem],
  intros y Hy, have := of_nat_of_mem_of_nat Hy, cases this with j Hj,
  rw[mem.congr_left Hj], use j, simp[equiv.refl]
end

lemma is_ewo_omega : epsilon_well_orders (omega : pSet.{u}) :=
begin
  refine ⟨_,_⟩,
    {intros y Hy z Hz, cases Hy, cases Hz, cases Hy_w with k₁, cases Hz_w with k₂,
     dsimp at Hy_h Hz_h, have := lt_trichotomy k₁ k₂, cases this, swap, cases this,
     subst this, left, from equiv.euc Hy_h ‹_›,
     right, right, rw[mem.congr_left ‹_›], rw[mem.congr_right Hy_h],
     from of_nat_mem_of_lt ‹_›, right, left, rw[mem.congr_left Hy_h], rw[mem.congr_right Hz_h],
     from of_nat_mem_of_lt ‹_›},
    {intros u Hu Hu_ne_empty,
     by_contra, push_neg at a,
     replace Hu_ne_empty := Set.regularity ⟦u⟧ (not_empty_of_not_equiv_empty ‹_›),
     rcases Hu_ne_empty with ⟨y,⟨Hy₁, Hy₂⟩⟩,
     specialize a (quotient.out y), cases a, suffices : y ∉ ⟦u⟧, by contradiction,
     {rw[mem_iff] at a, convert a, rw[quotient.out_eq]},
     cases a with z Hz, cases Hz with Hz₁ Hz₂,
     have : ⟦z⟧ ∈ (⟦u⟧ ∩ y : Set),
       by {apply Set.mem_inter.mpr, rw[<-mem_iff], use ‹_›,
           rw[mem_iff] at Hz₂, convert Hz₂, rw[quotient.out_eq]},
     apply Set.mem_empty ⟦z⟧, rwa[Hy₂] at this}
end

lemma Ord_omega : Ord (omega : pSet) := ⟨is_ewo_omega, is_transitive_omega⟩

lemma of_nat_inj {n k : ℕ} (H_neq : n ≠ k) : ¬ (pSet.equiv (of_nat n : pSet.{u}) (of_nat k : pSet.{u})) :=
begin
  intro H, replace H := (equiv.ext _ _).mp H, cases H with H₁ H₂,
  apply H_neq, apply le_antisymm; from le_of_subset ‹_›
end

-- lemma AE_of_AE_inj_indexing {x y : pSet} (H₁ : function.injective x.func) (H₂ : function.injective y.func) (H₂ : ∀ z ∈ y, ∃ w ∈ x,

lemma function_lift_aux {x y f : pSet}
 (H_func : is_func x y f) {i : type x}
 : ∃ (j : type y), Set.pair ⟦func x i⟧ ⟦func y j⟧ ∈ ⟦f⟧ :=
begin
  rcases H_func with ⟨f,Hf⟩, specialize Hf ⟦x.func i⟧ (by rw[<-mem_iff]; exact mem.mk'),
  rcases Hf with ⟨w, Hw₁, Hw₂⟩,
  have w_mem : w ∈ ⟦y⟧ :=
  (Set.pair_mem_prod.mp (Set.subset_iff_all_mem.mp _ _ Hw₁)).right,
  rw[show w = ⟦w.out⟧, by rw[quotient.out_eq]] at w_mem,
  rw[<-mem_iff, mem_unfold] at w_mem,
  cases w_mem with j Hj, use j,
  have : ⟦quotient.out w⟧ = ⟦func y j⟧ := quotient.sound Hj,
  rw[<-this], convert Hw₁, rw[quotient.out_eq],
  swap, exact f
end

lemma function_lift'_aux {x y f : pSet}
 (H_func : is_weak_func x y f) {i : type x}
 : ∃ (j : type y), Set.pair ⟦func x i⟧ ⟦func y j⟧ ∈ ⟦f⟧ :=
begin
  rename H_func Hf, specialize Hf ⟦x.func i⟧ (by rw[<-mem_iff]; exact mem.mk'),
  rcases Hf with ⟨w, ⟨Hw₁, Hw₁'⟩, Hw₂⟩,
  have w_mem : w ∈ ⟦y⟧ := ‹_›
  -- (Set.pair_mem_prod.mp (Set.subset_iff_all_mem.mp _ _ Hw₁)).right
  ,
  rw[show w = ⟦w.out⟧, by rw[quotient.out_eq]] at w_mem,
  rw[<-mem_iff, mem_unfold] at w_mem,
  cases w_mem with j Hj, use j,
  have : ⟦quotient.out w⟧ = ⟦func y j⟧ := quotient.sound Hj,
  rw[<-this], convert Hw₁', exact (quotient.out_eq _)
end
/--
  Given a function between pSets, lift it to a function on their underlying types.
-/
def function_lift {x y : pSet} (f : pSet) (H_func : is_func x y f) : x.type → y.type :=
λ i, classical.some (function_lift_aux ‹_› : ∃ j : y.type, Set.pair ⟦x.func i⟧ ⟦y.func j⟧ ∈ ⟦f⟧)

def function_lift' (x y : pSet) (f : pSet) (H_func : is_weak_func x y f) : x.type → y.type :=
λ i, classical.some (function_lift'_aux ‹_› : ∃ j : y.type, Set.pair ⟦x.func i⟧ ⟦y.func j⟧ ∈ ⟦f⟧)

lemma function_lift_spec {x y : pSet} {f} {H_func} {i : x.type} : Set.pair ⟦x.func i⟧ ⟦y.func (function_lift f H_func i)⟧ ∈ ⟦f⟧ :=
classical.some_spec (function_lift_aux ‹_›)

lemma function_lift'_spec {x y : pSet} {f} {H_func} {i : x.type} : Set.pair ⟦x.func i⟧ ⟦y.func (function_lift' x y f H_func i)⟧ ∈ ⟦f⟧ :=
classical.some_spec (function_lift'_aux ‹_›)

/--
  An easy consequence of function_lift_spec: if the lift of f sends i to j, then the corresponding pair of pSets lives in f.
-/
lemma mem_fun_of_function_lift_graph {x y : pSet} {f} {H_func} : ∀ i j, (function_lift f H_func) i = j → Set.pair ⟦(x.func i)⟧ ⟦(y.func j)⟧ ∈ ⟦f⟧ :=
by {intros _ _ H, rw[<-H], exact function_lift_spec}

lemma mem_fun_of_function_lift'_graph {x y : pSet} {f} {H_func} : ∀ i j, (function_lift' x y f H_func) i = j → Set.pair ⟦(x.func i)⟧ ⟦(y.func j)⟧ ∈ ⟦f⟧ :=
by {intros _ _ H, rw[<-H], exact function_lift'_spec}

/--
  If, in addition, the indexing function `y.func` is injective, f determines function_lift of f.
-/
lemma function_lift_graph_of_mem_fun_inj {x y : pSet} {f} {H_func} (H_inj : ∀ j₁ j₂ : y.type, equiv (y.func j₁) (y.func j₂) → j₁ = j₂) :
  ∀ i j, Set.pair ⟦(x.func i)⟧ ⟦(y.func j)⟧ ∈ ⟦f⟧ → (function_lift f H_func) i = j :=
begin
  intros i j H, unfold is_func Set.is_func at H_func,
  cases H_func with H_dom H_ext, specialize H_ext ⟦x.func i⟧ (Set.mem.mk'),
  rcases H_ext with ⟨w, Hw₁, Hw₂⟩,
  apply H_inj, apply equiv_of_eq, transitivity w,
    { apply Hw₂, exact function_lift_spec },
    { symmetry, exact Hw₂ _ ‹_› }
end

lemma function_lift'_graph_of_mem_fun_inj {x y : pSet} {f} {H_func} (H_inj : ∀ j₁ j₂ : y.type, equiv (y.func j₁) (y.func j₂) → j₁ = j₂) :
  ∀ i j, Set.pair ⟦(x.func i)⟧ ⟦(y.func j)⟧ ∈ ⟦f⟧ → (function_lift' x y f H_func) i = j :=
begin
  intros i j H, unfold is_weak_func at H_func,
  rename H_func H_ext, specialize H_ext ⟦x.func i⟧ (Set.mem.mk'),
  rcases H_ext with ⟨w, ⟨Hw₁, Hw₁'⟩, Hw₂⟩,
  apply H_inj, apply equiv_of_eq, transitivity w,
    { apply Hw₂, refine ⟨_,_⟩,
      { rw[<-mem_iff], exact mem.mk'},
      { exact function_lift'_spec } },
    { exact (Hw₂ _ ⟨Set.mem.mk',‹_›⟩).symm }
end

/--
  As a consequence of the previous lemma, if f is pSet-surjective then its lift is Lean-surjective.
-/
lemma surj_lift {x y : pSet} {f} {H_func : is_func x y f} (H_inj : ∀ j₁ j₂ : y.type, equiv (y.func j₁) (y.func j₂) → j₁ = j₂) (H_surj : is_surj x y f) :
  function.surjective (function_lift f H_func)
:=
begin
  intro j,
  suffices this : ∃ i : x.type, Set.pair ⟦x.func i⟧ ⟦y.func j⟧ ∈ ⟦f⟧,
    by {cases this with i Hi, exact ⟨i, function_lift_graph_of_mem_fun_inj ‹_› _ _ Hi⟩},
  unfold is_surj at H_surj, specialize H_surj (y.func j) (mem.mk'),
  rcases H_surj with ⟨z_i, ⟨Hz_i₁, Hz_i₂⟩⟩, rw[mem_unfold] at Hz_i₁,
  cases Hz_i₁ with j H_j, use j, convert Hz_i₂ using 2,
  simpa[equiv_iff_eq] using H_j.symm
end

lemma surj_lift' {x y : pSet} {f} {H_func} (H_inj : ∀ j₁ j₂ : y.type, equiv (y.func j₁) (y.func j₂) → j₁ = j₂) (H_surj : is_surj x y f) :
  function.surjective (function_lift' x y f H_func)
:=
begin
  intro j,
  suffices this : ∃ i : x.type, Set.pair ⟦x.func i⟧ ⟦y.func j⟧ ∈ ⟦f⟧,
    by {cases this with i Hi, exact ⟨i, function_lift'_graph_of_mem_fun_inj ‹_› _ _ Hi⟩},
  unfold is_surj at H_surj, specialize H_surj (y.func j) (mem.mk'),
  rcases H_surj with ⟨z_i, ⟨Hz_i₁, Hz_i₂⟩⟩, rw[mem_unfold] at Hz_i₁,
  cases Hz_i₁ with j H_j, use j, convert Hz_i₂ using 2,
  simpa[equiv_iff_eq] using H_j.symm
end

lemma ex_no_surj_omega_aleph_one : ¬ ∃ f : pSet, is_func (pSet.omega) (card_ex $ aleph 1) f ∧ (is_surj (pSet.omega) (card_ex $ aleph 1) f) :=
begin
  intro H,
  suffices this : ∃ g : pSet.omega.type → (card_ex $ aleph 1).type, function.surjective g,
    by {cases this with g Hg,
        suffices H_bad : #((card_ex $ aleph 1).type) ≤ # pSet.omega.type,
          by { simp at H_bad, exact not_lt_of_le ‹_› (by simp) },
        exact mk_le_of_surjective Hg},
    rcases H with ⟨f, Hf, Hf'⟩,
    refine ⟨_,_⟩,
      { exact function_lift f ‹_› },
      { refine surj_lift _ ‹_›, intros j₁ j₂,
         contrapose, apply ordinal.mk_inj }
end

lemma ex_no_surj_omega_aleph_one' : ¬ ∃ f : pSet, is_weak_func (pSet.omega) (card_ex $ aleph 1) f ∧ (is_surj (pSet.omega) (card_ex $ aleph 1) f) :=
begin
  intro H,
  suffices this : ∃ g : pSet.omega.type → (card_ex $ aleph 1).type, function.surjective g,
    by {cases this with g Hg,
        suffices H_bad : #((card_ex $ aleph 1).type) ≤ # pSet.omega.type,
          by { simp at H_bad, exact not_lt_of_le ‹_› (by simp) },
        exact mk_le_of_surjective Hg},
    rcases H with ⟨f, Hf, Hf'⟩,
    refine ⟨_,_⟩,
      { exact function_lift' _ _ f ‹_› },
      { refine surj_lift' _ ‹_›, intros j₁ j₂,
         contrapose, apply ordinal.mk_inj }
end

def pair (x y : pSet.{u}) : pSet.{u} := {{x}, {x,y}}

lemma pair_sound {x y : pSet.{u}} : ⟦pair x y⟧ = Set.pair ⟦x⟧ ⟦y⟧ := sorry

lemma eq_iff_eq_pair {x y x' y' : pSet.{u}} : pSet.equiv x x' ∧ pSet.equiv y y' ↔ pSet.equiv (pair x y) (pair x' y') := sorry

def prod (x y : pSet.{u}) : pSet.{u} :=
⟨x.type × y.type, (λ pr, pair (x.func pr.1) (y.func pr.2))⟩

-- ∃ x, p x ∧ ∀ y, p y → y = x

--f ⊆ prod x y ∧ ∀z:Set.{u}, z ∈ x → ∃! w, pair z w ∈ f
lemma is_func_iff {x y f : pSet.{u}} :
  is_func x y f ↔ f ⊆ prod x y ∧ ∀ z, z ∈ x → (∃ w, pair z w ∈ f ∧
                  ∀ v, pair z v ∈ f → pSet.equiv v w) :=
begin
  sorry
end

def set_of_indicator {x : pSet.{u}} (χ : x.type → Prop) : pSet.{u} :=
⟨{i // χ i}, λ p, x.func (p.1)⟩

def functions (x y : pSet.{u}) : pSet.{u} := -- TODO(jesse): show this satisfies specification
@set_of_indicator (powerset $ prod x y)
  (λ i_S, is_func x y ((powerset $ prod x y).func i_S))

lemma mem_functions_iff {x y : pSet.{u}} (z : pSet.{u}) : z ∈ functions x y ↔ is_func x y z :=
sorry

@[simp]lemma zero_lt_omega : 0 < ordinal.omega := omega_pos

@[simp]lemma card_ex_aleph_exists_mem {n : ℕ} : ∃ z, z ∈ card_ex (aleph n) :=
begin
  use (card_ex 0), unfold card_ex, apply mk_mem_mk_of_lt,
  induction n with n ih,
    { simp },
    { from lt_trans ih (by {simp, sorry}) }
end

end pSet
