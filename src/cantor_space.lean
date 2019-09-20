/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
import .regular_open_algebra

universes u v
local attribute [instance] classical.prop_decidable

/- Some facts about Cantor spaces: topological spaces of the form (set α) -/

open topological_space lattice

@[instance, priority 1000]def Prop_space : topological_space Prop := ⊥

instance discrete_Prop : discrete_topology Prop := ⟨rfl⟩

instance product_topology {α : Type*} : topological_space (set α) :=
Pi.topological_space

lemma eq_true_of_provable {p : Prop} (h : p) : (p = true) := by simp[h]

lemma eq_false_of_provable_neg {p : Prop} (h : ¬ p) : (p = false) := by finish

@[reducible, simp]noncomputable def Prop_to_bool (p : Prop) : bool :=
by {haveI := classical.prop_decidable p, by_cases p, exact true, exact false}

@[simp]lemma Prop_to_bool_true : Prop_to_bool true = tt := by simp

@[simp]lemma Prop_to_bool_false : Prop_to_bool false = ff := by simp

noncomputable def equiv_Prop_bool : equiv Prop bool :=
{ to_fun := Prop_to_bool,
  inv_fun := λ b, by {cases b, exact false, exact true},
  left_inv := λ p, by {by_cases p, rw[eq_true_of_provable h, Prop_to_bool_true],
                        rw[eq_false_of_provable_neg h, Prop_to_bool_false]},
  right_inv := λ x, by cases x; finish }

noncomputable instance Prop_encodable : encodable Prop :=
 @encodable.of_equiv _ _ (by apply_instance) equiv_Prop_bool

instance Prop_separable : separable_space Prop :=
{ exists_countable_closure_eq_univ :=
  by {use set.univ, refine ⟨set.countable_encodable _, by simp⟩}}

@[ematch]lemma is_open_of_compl_closed {α : Type*} [topological_space α] {S : set α} (H : (: is_closed (-S) :)) : is_open S :=
by rwa[<-is_closed_compl_iff]

@[ematch]lemma is_closed_of_compl_open {α : Type*} [topological_space α] {S : set α} (H : (: is_open (-S) :)) : is_closed S :=
by rwa[<-is_open_compl_iff]

def clopens (α : Type*) [topological_space α] : Type* := {S : set α // is_clopen S}

instance clopens_lattice {α : Type*} [topological_space α] : lattice (clopens α) :=
{ sup := λ S₁ S₂, ⟨S₁.1 ∪ S₂.1, by {apply is_clopen_union, tidy}⟩,
  le := λ S₁ S₂, S₁.1 ⊆ S₂.1,
  lt := λ S₁ S₂, S₁.1 ⊆ S₂.1 ∧ S₁.1 ≠ S₂.1,
  le_refl := by tidy,
  le_trans := by tidy,
  lt_iff_le_not_le :=
    by {intros; split; intros,
      {split, {from a_1.left},
        intro H, apply a_1.right, refine le_antisymm _ _, from a_1.left, from ‹_›},
        {/- `tidy` says -/ cases a_1, cases b, cases a, cases a_property,
        cases b_property, dsimp at *, fsplit,
        work_on_goal 0 { assumption }, intros a, induction a, solve_by_elim}},
  le_antisymm := by {intros, apply subtype.eq, refine le_antisymm _ _; from ‹_›},
  le_sup_left := by {intros, simp, intros x Hx, left, from ‹_›},
  le_sup_right := by {intros, simp, intros x Hx, right, from ‹_›},
  sup_le := by {intros, intros x Hx, cases Hx, from a_1 ‹_›, from a_2 ‹_›},
  inf := λ S₁ S₂, ⟨S₁.1 ∩ S₂.1, by {apply is_clopen_inter, from S₁.property, from S₂.property}⟩,
  inf_le_left := by {intros, simp, intros x Hx, from Hx.left},
  inf_le_right := by {intros, simp, intros x Hx, from Hx.right},
  le_inf := by {intros, simp, intros x Hx, from ⟨a_1 ‹_›, a_2 ‹_›⟩}}

instance clopens_bounded_lattice {α : Type*} [topological_space α] : bounded_lattice (clopens α) :=
{top := ⟨set.univ, is_clopen_univ⟩,
  le_top := by tidy,
  bot := ⟨∅, is_clopen_empty⟩,
  bot_le := by tidy,
 .. clopens_lattice}

noncomputable def finset_clopens_mk {α : Type*} [topological_space α] {X : finset (set α)} (H : ∀ S ∈ X, is_clopen S) : finset (clopens α) :=
begin
  apply finset.image, show finset _, from finset.attach X,
  intro x, cases x with x Hx, use x, from H x Hx
end

lemma is_clopen_finite_inter {α : Type*} [topological_space α] {X : finset (set α)}
  (H_X : ∀ S ∈ X, is_clopen S) : is_clopen (finset.inf X id) :=
begin
  revert H_X, apply finset.induction_on X, intro _, from is_clopen_univ,
  intros a A H_a H_A IH, simp at ⊢ IH, apply is_clopen_inter,
  from IH a (or.inl rfl), apply H_A, intros S H_S, from IH S (or.inr H_S)
end

lemma is_clopen_finite_inter' {α α' : Type*} [topological_space α] {X : finset α'} {f : α' → set (α)} (H_f : ∀ x ∈ X, is_clopen (f x)) : is_clopen (finset.inf X f) :=
begin
  revert H_f, apply finset.induction_on X, intro _, from is_clopen_univ,
  intros a A H_a H_A IH, simp at ⊢ IH, apply is_clopen_inter,
  from IH a (or.inl rfl), apply H_A, intros S H_S, from IH S (or.inr H_S)
end

namespace cantor_space
section cantor_space
variables {α : Type*}

def principal_open (x : α) : set (set α) := {S | x ∈ S}

def co_principal_open (x : α) : set (set α) := {S | x ∉ S}

@[simp]lemma neg_principal_open {x : α} : co_principal_open x = -(principal_open x)  :=
by unfold principal_open; refl

@[simp]lemma neg_co_principal_open {x : α} : - (co_principal_open x) = principal_open x :=
by {simp[principal_open]}

-- lemma is_open_induced_iff' {α β : Type*} {f : α → β} [t : topological_space β] {s : set α} {f : α → β} :
--    (∃t, is_open t ∧ f ⁻¹' t = s) ↔ @topological_space.is_open α (t.induced f) s := is_open_induced_iff.symm

def opens_over (x : α) : set(set(set α)) := {principal_open x, co_principal_open x, set.univ, ∅}

@[simp]lemma principal_open_mem_opens_over {x : α} : principal_open x ∈ opens_over x :=
by {right,right,right, from set.mem_singleton _}

@[simp]lemma co_principal_open_mem_opens_over {x : α} : co_principal_open x ∈ opens_over x :=
by {right,right,left, refl}

@[simp]lemma univ_mem_opens_over {x : α} : set.univ ∈ opens_over x :=
by {right,left, refl}

@[simp]lemma empty_mem_opens_over {x : α} : ∅ ∈ opens_over x :=
by {left, refl}

/-- Given a : α, τ is the topology induced by pulling back the
  discrete topology on Prop along the a'th projection map -/
def τ (a : α) : topological_space (set α) :=
induced (λS, a ∈ S) (by apply_instance : topological_space Prop)

lemma fiber_over_false {α : Type*} {a : α} : (λ x : set α, a ∈ x) ⁻¹' {false} = {y | a ∉ y} :=
begin
  ext, split; simp[set.mem_preimage]
end

lemma fiber_over_true {α : Type*} {a : α} : (λ x : set α, a ∈ x) ⁻¹' {true} = {y | a ∈ y} :=
begin
  ext, split; simp[set.mem_preimage]
end

lemma opens_over_sub_τ (a : α) : opens_over a ⊆ (τ a).is_open :=
begin
  unfold τ, intros S HS, unfold opens_over at HS,
  repeat{cases HS}, apply is_open_empty, apply _root_.is_open_univ,
  apply is_open_induced_iff.mpr, fsplit, exact {false}, fsplit,
  apply is_open_discrete,
    {ext1, ext1, dsimp at *, fsplit,
      work_on_goal 0 { intros a_1 a_2, cases a_1,
      work_on_goal 1 { assumption } }, work_on_goal 1 { intros a_1 },
    rwa[<-a_1], rwa[fiber_over_false]},
  apply is_open_induced_iff.mpr, fsplit, exact {true}, fsplit,
  apply is_open_discrete,
    {ext1, ext1, fsplit,
      work_on_goal 0 { intros a_1, cases a_1, work_on_goal 0 { cc },
      dsimp at a_1, cases a_1 }, intros a_1, rwa[fiber_over_true]},
end

lemma opens_over_le_τ (a : α) : τ a ≤ generate_from (opens_over a) :=
by { rw [le_generate_from_iff_subset_is_open], exact opens_over_sub_τ a }

lemma τ_le_product_topology (a : α) : product_topology ≤ τ a :=
infi_le _ _

lemma le_iff_opens_sub {β : Type*} {τ₁ τ₂ : topological_space β} :
  τ₂ ≤ τ₁ ↔ {S | τ₁.is_open S} ⊆ {S | τ₂.is_open S} := by refl

lemma τ_le_opens_over (a : α) : generate_from (opens_over a) ≤ τ a :=
begin
  apply le_iff_opens_sub.mpr, rintros X ⟨H_w, H_h_left, rfl⟩,
   by_cases htrue : true ∈ H_w; by_cases hfalse : false ∈ H_w,
   { constructor, unfold opens_over, repeat{split}, right,left,
    ext, by_cases a ∈ x, split, from λ _, trivial, intro, simp[h], from ‹_›,
    split, from λ _, trivial, intro, simp[h], from ‹_›},
   { constructor, unfold opens_over, repeat{split}, right, right, right,
     simp, ext, by_cases a ∈ x, split, intro H, simp[principal_open], from ‹_›,
     intro H, simp*, split; intros, simp [h, hfalse] at a_1, cases a_1,
     simp[principal_open, *, -a_1] at a_1, cases a_1},
   { constructor, unfold opens_over, repeat{split}, right, right, left,
     simp, ext, split; intros; simp[*, -a_1] at a_1; by_cases a ∈ x,
     tidy {tactics := with_cc}, },
   { have : H_w = ∅, ext, split; intros, by_cases x; simp* at a_1; cases a_1, cases a_1,
    subst this, simp, by apply @is_open_empty _ (generate_from _)}
end

@[simp]lemma is_open_generated_from_basic {β : Type*} [topological_space β] {s : set (set β)} {x ∈ s} :
  is_open (generate_from s) x := by {constructor, from ‹_›}

lemma is_open_principal_open {a : α} : is_open (principal_open a) :=
by { apply (le_trans (τ_le_product_topology _) (opens_over_le_τ a)), simp[opens_over] }

lemma is_open_co_principal_open {a : α} : is_open (co_principal_open a) :=
by { apply (le_trans (τ_le_product_topology _) (opens_over_le_τ a)), simp[opens_over] }

lemma is_closed_principal_open {a : α} : is_closed (principal_open a) :=
by {apply is_closed_of_compl_open, from is_open_co_principal_open}

lemma is_closed_co_principal_open {a : α} : is_closed (co_principal_open a) :=
by {apply is_closed_of_compl_open,
    simp only [neg_principal_open, lattice.neg_neg], from is_open_principal_open}

lemma is_clopen_principal_open {a : α} : is_clopen (principal_open a) :=
  ⟨is_open_principal_open, is_closed_principal_open⟩

lemma is_clopen_co_principal_open {a : α} : is_clopen (co_principal_open a) :=
  ⟨is_open_co_principal_open, is_closed_co_principal_open⟩

@[reducible]def principal_open_finset (F : finset α) : set (set α) := {S | F.to_set ⊆ S}

@[simp]lemma principal_open_finset_insert {F : finset α} {a : α} : principal_open_finset (insert a F) = principal_open_finset {a} ∩ principal_open_finset F :=
begin
  ext, split; intros; unfold principal_open_finset at *,
  tidy, apply a_1, unfold finset.to_set, simp,
  apply a_1, unfold finset.to_set at *, simp, right, from a_3,
  unfold finset.to_set at *, simp at *, cases a_3,
  apply a_1_left, from a_3, apply a_1_right, from a_3
end

lemma principal_open_finset_eq_inter (F : finset α) : principal_open_finset F = (finset.inf F (principal_open)) :=
begin
  apply finset.induction_on F,
    {tidy},
  intros a A h_a IH, simp, rw[<-IH], ext, split; intros,
  tidy, apply a_1_left, simp[finset.to_set]
end

@[reducible] def co_principal_open_finset (F : finset α) : set (set α) := {S | F.to_set ⊆ (-S)}

@[simp]lemma co_principal_open_finset_insert {F : finset α} {a : α} : co_principal_open_finset (insert a F) = co_principal_open_finset {a} ∩ co_principal_open_finset F :=
begin
  ext, split; intros; unfold co_principal_open_finset at *,
  split, intros a_2 H, simp at a_1, apply a_1, unfold finset.to_set at ⊢ H,
  {tidy}, intros a_2 H, simp at a_1, apply a_1, unfold finset.to_set at ⊢ H,
  {tidy, right, from ‹_›}, intros a_2 H, simp[finset.to_set] at *,
  cases H; [apply a_1.left, apply a_1.right]; simpa
end

lemma co_principal_open_finset_eq_inter (F : finset α) : co_principal_open_finset F = (finset.inf F (co_principal_open)) :=
begin
  apply finset.induction_on F,
    {tidy},
  intros a A h_a IH, simp, rw[<-IH], ext, split; intros,
  tidy, apply a_1_left, simp[finset.to_set], from a_1
end

lemma is_clopen_principal_open_finset (F : finset α) : is_clopen (principal_open_finset F) :=
begin
  rw[principal_open_finset_eq_inter], apply is_clopen_finite_inter',
  from λ _ _, is_clopen_principal_open
end

lemma is_clopen_co_principal_open_finset (F : finset α) : is_clopen (co_principal_open_finset F) :=
begin
  rw[co_principal_open_finset_eq_inter], apply is_clopen_finite_inter',
  from λ _ _, is_clopen_co_principal_open
end

lemma product_topology_generate_from : (product_topology : topological_space (set α)) = generate_from (⋃(a : α), opens_over a) :=
begin
  apply le_antisymm,
  { unfold product_topology Pi.topological_space,
    apply generate_from_mono,
    intros X HX, rcases HX with ⟨W, ⟨H₁, H₂⟩⟩, simp, cases H₁ with a Ha,
    use τ a, split, use a, refl, apply opens_over_le_τ a, constructor, cc },
  refine le_infi _, intro a,
  refine le_trans _ (τ_le_opens_over a), apply generate_from_mono,
  intros X H, constructor, simp, use a, exact H
end

def standard_basis : set (set (set α)) :=
{T : set (set α) | ∃ p_ins p_out : finset α, T = (finset.inf p_ins principal_open) ∩ (finset.inf p_out co_principal_open) ∧ p_ins ∩ p_out = ∅} ∪ {∅}

lemma ins₁_out₂_disjoint {x : set α} {p_ins₁ p_out₁ p_ins₂ p_out₂ : finset α}
  (H_mem₁ : x ∈ finset.inf p_ins₁ principal_open ∩ finset.inf p_out₁ co_principal_open)
  (H_mem₂ : x ∈ finset.inf p_ins₂ principal_open ∩ finset.inf p_out₂ co_principal_open)
  (H_disjoint₁ : p_ins₁ ∩ p_out₁ = ∅) (H_disjoint₂ : p_ins₂ ∩ p_out₂ = ∅)
  {a : α} (Ha_left : a ∈ p_ins₁)
  (Ha_right : a ∈ p_out₂) : false :=
begin
  rw[<-principal_open_finset_eq_inter, <-co_principal_open_finset_eq_inter] at H_mem₁ H_mem₂,
  suffices : a ∉ x ∧ a ∈ x, from (not_and_self _).mp this, split,
  rw[set.mem_inter_iff] at H_mem₂, apply H_mem₂.right ‹_›,
  rw[set.mem_inter_iff] at H_mem₁, apply H_mem₁.left ‹_›
end

@[simp]lemma principal_open_mem_standard_basis {a : α} : (principal_open a) ∈ (@standard_basis α) :=
by {simp[standard_basis], right, use {a}, use ∅, tidy}

@[simp]lemma co_principal_open_mem_standard_basis {a : α} : co_principal_open a ∈ (@standard_basis α) :=
by {simp[standard_basis], right, use ∅, use {a}, tidy}

lemma univ_mem_standard_basis : set.univ ∈ (@standard_basis α) :=
by {simp[standard_basis], use ∅, use ∅, tidy}

lemma intersection_standard_basis_nonempty' {α : Type*} {p_ins p_out : finset α} {H : p_ins ∩ p_out = ∅} : ∃ X, X ∈ finset.inf p_ins principal_open ∩ finset.inf p_out co_principal_open :=
begin
  use p_ins.to_set, rw[<-principal_open_finset_eq_inter, <-co_principal_open_finset_eq_inter],
  simp[finset.to_set], intros x Hx, simp, intro H', apply ((finset.ext).mp H x).mp,
  rw[finset.mem_inter], from ⟨‹_›,‹_›⟩
end

lemma intersection_standard_basis_nonempty {α : Type*} {T : set (set α)} {p_ins p_out : finset α} {H_eq : T = finset.inf p_ins principal_open ∩ finset.inf p_out co_principal_open} {H : p_ins ∩ p_out = ∅} : ¬⋂₀ finset.to_set (finset.image principal_open p_ins ∪ finset.image co_principal_open p_out) = ∅ :=
begin
  intro H', simp[finset.to_set] at H', replace H' := (set.ext_iff _ _).mp H',
  cases @intersection_standard_basis_nonempty' _ p_ins p_out ‹_› with a H_a, subst H_eq,
  rw[<-principal_open_finset_eq_inter, <-co_principal_open_finset_eq_inter] at H_a, cases H_a,
  specialize H' a, apply H'.mp, simp, simp[not_forall] at H',
  rcases H' with ⟨s, ⟨⟨w', Hw'_1, Hw'_2⟩, H_a'⟩⟩; intros t Ht; cases Ht;
  rcases Ht with ⟨w, H_w, H_w_eq⟩; subst H_w_eq, tidy
end


lemma standard_basis_reindex {α : Type*} {T : set (set α)} {p_ins p_out : finset α} {H_eq : T = finset.inf p_ins principal_open ∩ finset.inf p_out co_principal_open} {H : p_ins ∩ p_out = ∅} : ⋂₀ finset.to_set (finset.image principal_open p_ins ∪ finset.image co_principal_open p_out) = T :=
begin
  subst H_eq, rw[<-principal_open_finset_eq_inter, <-co_principal_open_finset_eq_inter],
  simp[finset.to_set], ext; split; intro H',
    {rw[set.mem_sInter] at H',

    simp[principal_open_finset, co_principal_open_finset], split,
    intros a Ha, specialize H' (principal_open a), apply H',
    right, use a, from ⟨‹_›, rfl⟩,

    intros a Ha, specialize H' (co_principal_open a), apply H',
    left, use a, from ⟨‹_›, rfl⟩,},

    {rw[set.mem_sInter], intros T hT, simp at hT, cases hT,
    simp[finset.to_set] at H', tidy}
end

lemma is_topological_basis_standard_basis : @is_topological_basis (set α) _ standard_basis :=
begin
  repeat{split},
  {intros t₁ H₁ t₂ H₂ x Hx, cases H₁; cases H₂,
    {rcases H₁ with ⟨p_ins₁, p_out₁, H₁, H₁'⟩, rcases H₂ with ⟨p_ins₂, p_out₂, H₂, H₂'⟩,
      use (finset.inf (p_ins₁ ∪ p_ins₂) principal_open) ∩ (finset.inf (p_out₁ ∪ p_out₂) co_principal_open), split, swap, split,
    split, rw[<-principal_open_finset_eq_inter], unfold principal_open_finset,
    simp, intros a Ha, simp[finset.to_set] at Ha, subst H₁, subst H₂,
    simp at Hx, rcases Hx with ⟨⟨Hx1, Hx2⟩, Hx3, Hx4⟩, cases Ha,
    rw[<-principal_open_finset_eq_inter] at Hx1, apply Hx1, from Ha,
    rw[<-principal_open_finset_eq_inter] at Hx3, apply Hx3, from Ha,

    rw[<-co_principal_open_finset_eq_inter], unfold co_principal_open_finset,
    simp, intros a Ha, simp[finset.to_set] at Ha, subst H₁, subst H₂,
    simp at Hx, rcases Hx with ⟨⟨Hx1, Hx2⟩, Hx3, Hx4⟩, cases Ha,
    rw[<-co_principal_open_finset_eq_inter] at Hx2, apply Hx2, from Ha,
    rw[<-co_principal_open_finset_eq_inter] at Hx4, apply Hx4, from Ha,

    rw[<-principal_open_finset_eq_inter, <-co_principal_open_finset_eq_inter],
    intros a Ha, unfold principal_open_finset co_principal_open_finset at Ha,
    cases Ha with Ha₁ Ha₂, substs H₁ H₂, split,
    rw[<-principal_open_finset_eq_inter, <-co_principal_open_finset_eq_inter],
    split, intros x Hx, apply Ha₁, simp[finset.to_set], left, from Hx,
    intros x Hx, apply Ha₂, simp[finset.to_set], left, from Hx,

    rw[<-principal_open_finset_eq_inter, <-co_principal_open_finset_eq_inter],
    split, intros x Hx, apply Ha₁, simp[finset.to_set], right, from Hx,
    intros x Hx, apply Ha₂, simp[finset.to_set], right, from Hx,

    use (p_ins₁ ∪ p_ins₂), use (p_out₁ ∪ p_out₂), refine ⟨rfl, _⟩,
    simp only [finset.inter_distrib_left, finset.inter_distrib_right],
    ext1, split; intro Ha, swap, cases Ha, simp [H₁', H₂'] at Ha,
    repeat{cases Ha}; exfalso; substs H₁ H₂; cases Hx,
    from ins₁_out₂_disjoint Hx_left Hx_right ‹_› ‹_› Ha_left Ha_right,
    from ins₁_out₂_disjoint Hx_right Hx_left ‹_› ‹_› Ha_right Ha_left
    },
    {replace H₂ := set.mem_singleton_iff.mp H₂, subst H₂, exfalso, simpa using Hx},
    {replace H₁ := set.mem_singleton_iff.mp H₁, subst H₁, exfalso, simpa using Hx},
    {replace H₁ := set.mem_singleton_iff.mp H₁, subst H₁, exfalso, simpa using Hx}
  },
  {ext, split; intros, trivial, rw[set.mem_sUnion], use set.univ,
    use univ_mem_standard_basis},
  {rw[product_topology_generate_from], refine le_antisymm _ _, swap,

    {apply generate_from_mono,
     intros X H_X, rcases H_X with ⟨w, ⟨a, H_w⟩, H_X⟩,
     unfold standard_basis, simp, subst H_w, repeat{cases H_X}, left, refl,
     right, use ∅, use ∅, {simp, refl}, right, use ∅, use {a},
     {/- `tidy` says -/ simp, ext1,   fsplit, work_on_goal 0
     { intros a_1, fsplit, work_on_goal 0 { fsplit },
     fsplit, work_on_goal 0 { assumption },  fsplit },
     intros a_1 a_2, cases a_1, cases a_1_right, solve_by_elim}, right, use {a}, use ∅,
     {/- `tidy` says -/ simp, ext1, fsplit, work_on_goal 0
     { intros a_1, fsplit, work_on_goal 0 { fsplit, work_on_goal 0 { assumption }, fsplit },
     fsplit }, intros a_1, cases a_1, cases a_1_left, assumption}},

  {
  apply le_generate_from_iff_subset_is_open.mpr, intros T hT, unfold standard_basis at hT,
  cases hT with hT h_empty, swap, rw[set.mem_singleton_iff] at h_empty, subst h_empty,
  apply @is_open_empty _ (generate_from _),

  simp, have := is_topological_basis_of_subbasis (product_topology_generate_from), swap, from α,
  rw[<-product_topology_generate_from],
  apply is_open_of_is_topological_basis this, simp,
  rcases hT with ⟨p_ins, p_out, H_eq, H⟩,
  use ((finset.image principal_open p_ins) ∪ (finset.image co_principal_open p_out)).to_set,
  split, split, from finset.finite_to_set _, split,
  apply finset.induction_on p_ins, apply finset.induction_on p_out,
  simp, intros x Hx, cases Hx, intros a A H_a H_A, simp, intros x Hx,
  simp[finset.to_set] at Hx, cases Hx, rw[set.mem_Union], use a, rw[Hx],
  rw[<-neg_principal_open], from co_principal_open_mem_opens_over,
  rw[set.mem_Union], cases Hx with a Hx, use a, rw[<-Hx.right],
  rw[<-neg_principal_open], from co_principal_open_mem_opens_over,
  intros a A H_a H_A, simp, intros x Hx, simp[finset.to_set] at Hx, cases Hx,
  rw[Hx], rw[set.mem_Union], use a, from principal_open_mem_opens_over,
  cases Hx with Hx Hx', rw[set.mem_Union], cases Hx with a Hx,
  use a, rw[<-Hx.right, <-neg_principal_open], from co_principal_open_mem_opens_over,
  cases Hx' with a Hx, rw[set.mem_Union],
  use a, rw[<-Hx.right], from principal_open_mem_opens_over,

  by {apply intersection_standard_basis_nonempty; from ‹_›},

  by {apply standard_basis_reindex; from ‹_›}
}}
end

open cardinal

lemma countable_chain_condition_set {α : Type u} : countable_chain_condition (set α) :=
begin
  apply countable_chain_condition_pi, intros s hs,
  apply countable_chain_condition_of_countable, apply le_of_lt,
  convert @power_lt_omega (mk (ulift Prop)) (mk s) _ _ using 1,
  { refine quotient.sound ⟨equiv.arrow_congr (equiv.refl _) equiv.ulift.symm⟩ },
  { rw [prop_eq_two], convert cardinal.nat_lt_omega 2, rw [nat.cast_bit0, nat.cast_one] },
  rwa lt_omega_iff_finite
end

end cantor_space
end cantor_space

