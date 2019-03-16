import set_theory.ordinal set_theory.zfc tactic.tidy

open ordinal

open cardinal

noncomputable theory

local attribute [instance, priority 0] classical.prop_decidable
universe u
namespace pSet

@[reducible]def succ (x : pSet) : pSet := insert x x

@[reducible]noncomputable def ordinal.mk : ordinal.{u} → pSet.{u} :=
λ η, limit_rec_on η ∅ (λ ξ mk_ξ, pSet.succ mk_ξ)
begin
  intros ξ ξ_limit ih,
  refine ⟨ξ.out.α, λ x, ih (typein _ _) _⟩,
  from ξ.out.α, from ξ.out.r, from ξ.out.wo, from x,
  convert @typein_lt_type _ (ξ.out.r) (ξ.out.wo) x,
  unfold ordinal.type, conv{to_lhs, rw[<-quotient.out_eq ξ]},
  apply quotient.sound, cases quotient.out ξ, refl
end

@[simp]lemma ordinal.mk_zero : ordinal.mk 0 = ∅ := by simp[ordinal.mk]

@[simp]lemma ordinal.mk_succ {η η_pred : ordinal} {H_succ : η = ordinal.succ η_pred} : ordinal.mk η = pSet.succ (ordinal.mk η_pred) :=
by {rw[H_succ], simp[ordinal.mk]}

@[simp]lemma ordinal.mk_succ₂ {η : ordinal} : ordinal.mk (ordinal.succ η) = pSet.succ (ordinal.mk η) :=
by {simp[ordinal.mk]}

@[simp]lemma ordinal.mk_limit {η : ordinal} {H_limit : is_limit η} : ordinal.mk η = ⟨η.out.α, λ x, ordinal.mk (@typein _ (η.out.r) (η.out.wo) x)⟩ :=
by simp[*, ordinal.mk]

def epsilon_well_orders (x : pSet.{u}) : Prop :=
  (∀ y, y ∈ x → (∀ z, z ∈ x → (equiv y z ∨ y ∈ z ∨ z ∈ y))) ∧
  (∀ u, u ⊆ x → (¬ (equiv u (∅ : pSet.{u})) → ∃ y, (y ∈ u ∧ (∀ z', z' ∈ u → ¬ z' ∈ y))))

def is_transitive (x : pSet) : Prop := ∀ y, y ∈ x → y ⊆ x

def Ord (x : pSet) : Prop := epsilon_well_orders x ∧ is_transitive x

lemma equiv_of_eq {x y : pSet} : ⟦x⟧ = ⟦y⟧ → pSet.equiv x y :=
λ H, quotient.eq.mp H

instance mem_of_pSet : has_mem (quotient pSet.setoid) (quotient pSet.setoid) :=
{mem := Set.mem}

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

lemma subset_all_mem {x y : pSet} : y ⊆ x ↔ ∀ z, z ∈ y → z ∈ x :=
by {split; intros; [apply all_mem_of_subset, apply subset_of_all_mem], repeat{assumption}}

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

lemma mem_iff {x y : pSet} : x ∈ y ↔ ⟦x⟧ ∈ ⟦y⟧ := by refl

lemma Ord_empty : Ord (∅ : pSet.{u}) :=
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

lemma Ord_succ (x : pSet) (H : Ord x) : Ord (succ x) :=
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

lemma transitive_Union (x : pSet) (H : ∀ y ∈ x, is_transitive y) : is_transitive (Union x) :=
begin
  intros z Hz, apply subset_of_all_mem, intros w Hw,
  rw[mem_Union] at Hz, rcases Hz with ⟨y, ⟨Hy, Hy'⟩⟩,
  have H_trans := H y ‹_› z ‹_›, have := all_mem_of_subset ‹_› w ‹_›,
  apply mem_Union.mpr, use y, use ‹_›, from ‹_›
end

lemma transitive_mk (η : ordinal.{u}) : is_transitive $ ordinal.mk η :=
begin
  apply limit_rec_on η,
    simp[Ord_empty.right],
    intros ξ ih,
  simp, from transitive_succ _ ‹_›,
  intros ξ h_limit ih,

  simp*, intros y yH, sorry
end

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
    by {specialize H_trans y ‹_›, rw[subset_all_mem] at H_trans, specialize H_trans w ‹_›,
    exact H_trans},
  have H_z_in_x : z ∈ x,
    by {specialize H_trans w ‹_›, rw[subset_all_mem] at H_trans, from H_trans z ‹_›},
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

lemma mk_lt_of_lt {β₁ β₂ : ordinal.{u}} (H : β₁ < β₂) : ordinal.mk β₁ ∈ ordinal.mk β₂ :=
begin
  revert H, revert β₁, apply limit_rec_on β₂,
  intros β₁ H, exfalso, sorry, -- there is no principal segment in 0

  intro η, intro ih,
  intros ξ h_ξ,

  {haveI po_ord : partial_order ordinal.{u} := by apply_instance,
  have : ξ ≤ η, from ordinal.lt_succ.mp ‹_›,
  have this' := (@le_iff_lt_or_eq ordinal _ ξ η).mp ‹_›,
  cases this',
    {have this'' := @ih ξ ‹_›,
      suffices H : is_transitive (ordinal.mk (ordinal.succ η)),
      specialize H (ordinal.mk η) (by simp), rw[subset_all_mem] at H,
      from H (ordinal.mk ξ) ‹_›, apply transitive_mk},
    {rw[this'], simp}},

  intros η h_limit ih ξ hξ, simp only [h_limit, ordinal.mk_limit], sorry
  -- apply mem_Union.mpr, use (ordinal.mk (ordinal.succ ξ)), split,
  -- swap, simp, split, swap, -- to finish this, need a lemma which says that given a (ξ + 1) which is less than η, there exists an isomorphic initial segment in (quotient.out η)
  -- sorry, sorry
end

lemma mk_trichotomy (β₁ β₂ : ordinal.{u}) : (equiv (ordinal.mk β₁) (ordinal.mk β₂)) ∨ (ordinal.mk β₁) ∈ (ordinal.mk β₂) ∨ (ordinal.mk β₂) ∈ (ordinal.mk β₁) :=
begin
  have := lt_trichotomy β₁ β₂,
  repeat{cases this},
    right,left, from mk_lt_of_lt ‹_›,
    left, apply equiv.refl,
    right,right, from mk_lt_of_lt ‹_›
end

lemma ewo_Union (x : pSet) (H : ∀ y ∈ x, Ord y) : epsilon_well_orders (Union x) :=
begin
  split, swap,
    intros _ _ _, apply well_founded u ‹_›,

  intros y Hy z Hy,
    have this₁ : Ord y, by {sorry},
  sorry
end

lemma Ord_Union (x : pSet) (H : ∀ y ∈ x, Ord y) : Ord (Union x) :=
by {split, apply ewo_Union ‹_› ‹_›, apply transitive_Union,
    intros y h', apply (H _ _).right, from ‹_›}

lemma Ord_mk (η : ordinal) : Ord (ordinal.mk η) :=
sorry

end pSet
