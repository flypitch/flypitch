/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
import .set_theory order.complete_boolean_algebra topology.basic

local attribute [instance] classical.prop_decidable

open set

meta def not_as_big_bertha : tactic string := `[cc] >> pure "cc"

meta def not_as_big_bertha' : tactic string := `[{[smt] close}] >> pure "{[smt] close}"

meta def with_cc : list (tactic string) := tactic.tidy.default_tactics ++ [not_as_big_bertha]

meta def with_cc' : list (tactic string) := tactic.tidy.default_tactics ++ [not_as_big_bertha']

namespace topological_space
section topology_lemmas
variables {α : Type*} [τ : topological_space α]
local notation `cl`:65 := closure

local notation `int`:65 := interior

attribute [simp] interior_eq_of_open

include τ

def dense (S : set α) : Prop := ∀ U : set α, @is_open α τ U → U ≠ ∅ → U ∩ S ≠ ∅

lemma closure_univ_of_dense {S : set α} (H_dense : dense S) : closure S = univ :=
dense_iff_inter_open.mpr H_dense

/--
S is dense in the basis 𝓑 if S meets every B ∈ 𝓑.
-/
def dense_in_basis (S : set α) {𝓑 : set $ set α} (H_basis : is_topological_basis 𝓑) : Prop :=
∀ B ∈ 𝓑, B ≠ ∅ → B ∩ S ≠ ∅

lemma dense_of_dense_in_basis (S : set α) {𝓑} (H_basis : is_topological_basis 𝓑) (H : dense_in_basis S H_basis) : dense S :=
begin
  intros U HU HU_ne,
  cases (exists_mem_of_ne_empty ‹_›) with a Ha,
  rcases mem_basis_subset_of_mem_open ‹_› Ha ‹_› with ⟨B, ⟨HB₁, ⟨HB₂, HB₃⟩⟩⟩,
  suffices this : ∃ a', a' ∈ U ∧ a' ∈ S,
    from ne_empty_of_exists_mem this,
  have := exists_mem_of_ne_empty (H _ HB₁ (ne_empty_of_exists_mem (by finish))),
  rcases this with ⟨x,⟨Hx₁,Hx₂⟩⟩, use x, tidy
end

def nowhere_dense (S : set α) : Prop := int (cl S) = ∅

lemma frontier_closed_of_open {S : set α} (H : @is_open _ τ S) : is_closed (frontier S) :=
begin
  unfold frontier, rw[diff_eq], apply is_closed_inter, tidy
end

lemma frontier_nowhere_dense_of_open {S : set α} (H : @is_open _ τ S) : nowhere_dense (frontier S) :=
begin
  unfold nowhere_dense frontier,
  ext, split; intros, swap, cases a,
  rw[diff_eq] at a,
  rw[show cl(cl S ∩ -int S) = cl(S) ∩ -int S,
    by {apply closure_eq_of_is_closed, from frontier_closed_of_open H}] at a,
  rw[show int S = S, by {apply interior_eq_of_open, from ‹_›}] at a,
  rw[interior_inter] at a, simp at a, tidy
end

lemma is_clopen_interior {S : set α} (H : (: is_clopen S :)) : interior S = S :=
interior_eq_of_open H.left

local attribute [ematch] is_clopen_interior

lemma is_clopen_closure {S : set α} (H : (: is_clopen S :)) : closure S = S :=
closure_eq_of_is_closed H.right

local attribute [ematch] is_clopen_closure

@[simp]lemma closure_mono' {s t : set α} (H : (: s ⊆ t :)) : closure s ⊆ closure t ↔ true := by finish[closure_mono]

local attribute [ematch] closure_mono'

lemma closure_eq_compl_interior_compl' {s : set α} :
  closure s = - interior (- s) := closure_eq_compl_interior_compl

local attribute [ematch] closure_eq_compl_interior_compl'

lemma interior_compl' {s : set α} : interior (- s) = - closure s :=
by apply interior_compl

@[ematch]lemma interior_eq_compl_closure_compl {s : set α} :
  interior s = - closure (- s) :=
by ext; simp

lemma subset_anti {s t : set α} : -s ⊆ -t ↔ t ⊆ s :=
compl_subset_compl

lemma subset_anti' {s t : set α} (H : t ⊆ s) :  - (closure s) ⊆ - (closure t) :=
by finish[subset_anti]

local attribute [ematch] subset_anti'

lemma subset_anti_right {s t : set α} (H : s ⊆ -t) : s ⊆ -t ↔ t ⊆ -s :=
by {split, clear H, intro, rw[<-subset_anti], convert a, simp, finish}

local attribute [ematch] subset_anti_right

lemma compl_mono {s t : set α} (H : s ⊆ t) : - t ⊆ - s := by simp[*,subset_anti]

end topology_lemmas
end topological_space

open lattice
section regular
variables {α : Type*} [τ : topological_space α]

include τ
@[reducible]def topological_space.is_regular (S : set α) : Prop :=
 S = interior (closure S)

open topological_space

local attribute [ematch] is_clopen_interior is_clopen_closure closure_mono'
 is_regular subset_anti_right subset_anti' closure_eq_compl_interior_compl'

-- @[reducible,simp,ematch]def int_of_cl (S : set α) := interior (closure S)

def perp (S : set α) := - (closure S)
local attribute [reducible] perp

local postfix `ᵖ`:80 := perp

local notation `cl`:65 := closure

local notation `int`:65 := interior

@[reducible, ematch]lemma perp_unfold (S : set α) : Sᵖ = - (cl S) := rfl

@[simp]lemma is_open_perp {S : set α} : is_open (Sᵖ) :=
by {unfold perp, apply is_open_compl_iff.mpr, simp}

@[simp]lemma perp_univ : univᵖ = (∅ : set α) :=
by simp[perp_unfold]

@[simp]lemma perp_empty : (∅ : set α)ᵖ = univ :=
by simp[perp_unfold]

@[simp]lemma is_open_of_is_regular {S : set α} (H : (: is_regular S :)) : is_open S :=
by {unfold is_regular at H, rw[H], simp}

local attribute [ematch] is_open_of_is_regular

@[simp]lemma is_regular_of_clopen {S : set α} (H : is_clopen S) : is_regular S :=
by {[smt] eblast}

lemma regular_iff_p_p {S : set α} : is_regular S ↔ (Sᵖᵖ) = S :=
begin
  split; intro H, unfold is_regular at H,
  {[smt] eblast},
  {[smt] eblast}
end

lemma p_p_eq_int_cl {S : set α} : Sᵖᵖ = interior (closure S) :=
by {have := @regular_iff_p_p α _ S; {[smt] eblast}}

lemma int_cl_eq_p_p {S : set α} : int (cl S) = Sᵖᵖ := p_p_eq_int_cl.symm

@[ematch]lemma mem_int_cl_iff_mem_eq_p_p {S : set α} {a : α} : a ∈ int (cl S) ↔ a ∈ (Sᵖᵖ) := by rw[int_cl_eq_p_p]

lemma is_open_of_p_p {S : set α} (H : Sᵖᵖ = S) : is_open S :=
by {rw[p_p_eq_int_cl] at H, from is_open_of_is_regular (by {unfold is_regular, from H.symm})}

@[simp]lemma is_regular_empty : is_regular (∅ : set α) :=
by simp

@[simp]lemma is_regular_univ : is_regular (univ : set α) :=
by simp

lemma p_anti {P Q : set α} (H : P ⊆ Q) : Qᵖ ⊆ Pᵖ :=
by {have := subset_anti' H, from this}

lemma p_p_mono {P Q : set α} (H : P ⊆ Q) : Pᵖᵖ ⊆ Qᵖᵖ :=
p_anti $ p_anti H

lemma in_p_p_of_open {S : set α} (H : is_open S) : S ⊆ Sᵖᵖ :=
begin
  have : S ⊆ cl S := subset_closure,
  rw[<-subset_anti] at this,
  replace this := closure_mono this,
  rw[<-subset_anti] at this,
  convert this, simp*
end

lemma p_eq_p_p_p {S : set α} (H : is_open S) : Sᵖ = Sᵖᵖᵖ :=
begin
  have := p_anti (in_p_p_of_open ‹_›),
  have := in_p_p_of_open (show is_open (Sᵖ), by simp),
  ext; split; intros; solve_by_elim
end

@[simp]lemma p_p_p_p_eq_p_p {S : set α} : Sᵖᵖᵖᵖ = Sᵖᵖ :=
by {rw[<-p_eq_p_p_p], simp}

lemma is_regular_stable_subset {S₁ S₂ : set α} (H : is_regular S₂) (H₂ : S₁ ⊆ S₂) : S₁ᵖᵖ ⊆ S₂ :=
by {rw[regular_iff_p_p] at H,
   replace H₂ := p_anti (p_anti H₂), convert H₂, cc}

@[simp]lemma is_regular_eq_p_p {S : set α} (H : is_regular S) : Sᵖᵖ = S :=
begin
  refine le_antisymm _ _,
    apply is_regular_stable_subset ‹_›, intros _ _, from ‹_›,
  from in_p_p_of_open (is_open_of_is_regular ‹_›)
end

lemma subset_p_p_of_open {S : set α} (H : (: is_open S :)) : S ⊆ Sᵖᵖ :=
in_p_p_of_open ‹_›

lemma subset_int_cl_of_open {S : set α} (H : is_open S) : S ⊆ int (cl S) :=
by {rw[<-p_p_eq_int_cl], from subset_p_p_of_open ‹_›}

lemma is_regular_sup {S₁ S₂ : set α} : is_regular ((S₁ ∪ S₂)ᵖᵖ) :=
by rw[regular_iff_p_p]; simp

@[simp]lemma is_open_of_p_p' {S : set α} : is_open (Sᵖᵖ) :=
by {simp}

@[simp]lemma is_regular_p_p {S : set α} : is_regular (Sᵖᵖ) :=
begin
  refine le_antisymm _ _,
    rw[<-p_p_eq_int_cl], apply subset_p_p_of_open,
    apply is_open_of_p_p',
    rw[<-p_p_eq_int_cl], simp, intros _ _, from ‹_›
end

lemma inter_eq_inter_aux (S₁ S₂ : set α) (H : is_open S₁) : S₁ ∩ (cl S₂) ⊆ cl (S₁ ∩ S₂) :=
closure_inter_open ‹_›

@[simp]lemma cl_compl_of_is_open (S : set α) (H : is_open S) : cl(-S) = -S :=
by have : is_closed (-S); by simp*; simp[this]

lemma inter_eq_inter_aux₂ (S₁ S₂ : set α) {H₁ : is_open S₁} {H₂ : is_open S₂} : S₁ ∩ (S₂ᵖᵖ) ⊆ (S₁ ∩ S₂)ᵖᵖ :=
begin
    have this₃ := inter_eq_inter_aux S₁ S₂ H₁,
    have this₄ := compl_mono (this₃),
    rw[compl_inter] at this₄,
    have this₅ := p_anti this₄,
    unfold perp at this₅, rw[closure_union] at this₅,
    rw[cl_compl_of_is_open] at this₅, rw[compl_union] at this₅,
    convert this₅, simp, from ‹_›
end

lemma p_p_inter_eq_inter_p_p {S₁ S₂ : set α} (H₁ : is_open S₁) (H₂ : is_open S₂): (S₁ ∩ S₂)ᵖᵖ = S₁ᵖᵖ ∩ S₂ᵖᵖ :=
begin
  have this₀_left : S₁ ∩ S₂ ⊆ S₁, by simp,
  have this₀_right : S₁ ∩ S₂ ⊆ S₂, by simp,
  have this₁_left : (S₁ ∩ S₂)ᵖᵖ ⊆ S₁ᵖᵖ, from p_anti (p_anti this₀_left),
  have this₁_right : (S₁ ∩ S₂)ᵖᵖ ⊆ S₂ᵖᵖ, from p_anti (p_anti this₀_right),
  have this₂ : (S₁ ∩ S₂)ᵖᵖ ⊆ S₁ᵖᵖ ∩ S₂ᵖᵖ,
    by {intros x Hx, split, from this₁_left ‹_›, from this₁_right ‹_›},
  ext, split, from λ _, this₂ ‹_›,
  suffices : S₁ᵖᵖ ∩ S₂ᵖᵖ ⊆ (S₁ ∩ S₂)ᵖᵖ, from λ _, this ‹_›,
  have this₃ := inter_eq_inter_aux S₁ S₂ H₁,
  have this₄ := compl_mono (this₃),
  have this₅ := p_anti this₄,
  change _ ᵖ ⊆ _ ᵖᵖ at this₅,
  have this₆ : S₁ ∩ (S₂ᵖᵖ) ⊆ (S₁ ∩ S₂)ᵖᵖ,
    by {apply inter_eq_inter_aux₂; from ‹_›},
  have this₇ : (S₁ᵖᵖ) ∩ (S₂ᵖᵖ) ⊆ ((S₁ᵖᵖ) ∩ S₂)ᵖᵖ,
    by {apply inter_eq_inter_aux₂ (S₁ᵖᵖ), simpa},
  have this₈ : (S₂ ∩ S₁ᵖᵖ) ⊆ (S₂ ∩ S₁)ᵖᵖ,
    by {apply inter_eq_inter_aux₂ S₂ S₁; from ‹_›},
  have this₉ : (S₁ᵖᵖ ∩ S₂)ᵖᵖ ⊆ (S₁ ∩ S₂)ᵖᵖᵖᵖ,
    by {replace this₈ := p_anti this₈, replace this₈ := p_anti this₈,
        conv {congr, rw[inter_comm], skip, rw[inter_comm]}, from this₈},
  rw[<-p_eq_p_p_p] at this₉,
  from subset.trans this₇ this₉, from is_open_perp
end

@[simp]lemma is_regular_inter {S₁ S₂ : set α} (H₁ : is_regular S₁) (H₂ : is_regular S₂) : is_regular (S₁ ∩ S₂) :=
by {rw[regular_iff_p_p] at *, rw[p_p_inter_eq_inter_p_p (is_open_of_p_p H₁) (is_open_of_p_p H₂)], cc}

end regular

open topological_space

section regular_algebra

local postfix `ᵖ`:80 := perp

local notation `cl`:65 := closure

local notation `int`:65 := interior

variables {α : Type*} [τ : topological_space α]

include τ



variable (α)
@[reducible]def regular_opens := {S : set α // is_regular S}

local attribute [reducible] perp

variable{α}
def regular_open_poset : partial_order (regular_opens α) :=
{le := λ S₁ S₂, S₁.val ⊆ S₂.val,
  lt := λ S₁ S₂, S₁.val ⊆ S₂.val ∧ S₁.val ≠ S₂.val,
  le_refl := by {intro a, simp only},
  le_trans := by {intros a b c H₁ H₂, apply subset.trans H₁ H₂},
  lt_iff_le_not_le := by {intros a b, split; intro H, tidy,
                      suffices : a_val = b_val,
                      by contradiction, ext; intros; split; intros,
                         from H_left ‹_›, from a ‹_›},
  le_antisymm :=
    begin
      intros a b H₁ H₂, apply subtype.eq,
      ext; intros; split; intros, from H₁ ‹_›, from H₂ ‹_›
    end}
local attribute [instance] regular_open_poset

lemma le_iff_subset {S₁ S₂ : regular_opens α} : S₁ ≤ S₂ ↔ S₁.val ⊆ S₂ := by refl

def regular_open_lattice : lattice (regular_opens α) :=
{ sup := λ S₁ S₂, ⟨(S₁.val ∪ S₂.val)ᵖᵖ, by {apply is_regular_sup}⟩,
    le_sup_left :=
    begin
      intros a b, refine subset.trans (show a.val ⊆ a.val ∪ b.val, by simp) (show a.val ∪ b.val ⊆ (a.val ∪ b.val)ᵖᵖ, from _),
      apply subset_p_p_of_open (is_open_union (is_open_of_is_regular a.property) (is_open_of_is_regular b.property)),
    end,
  le_sup_right :=
    begin
      intros a b, refine subset.trans (show b.val ⊆ a.val ∪ b.val, by simp) (show a.val ∪ b.val ⊆ (a.val ∪ b.val)ᵖᵖ, from _),
      apply subset_p_p_of_open (is_open_union (is_open_of_is_regular a.property) (is_open_of_is_regular b.property)),
    end,
  sup_le := by {intros a b c H₁ H₂, apply is_regular_stable_subset, from c.property, intros x Hx, cases Hx; solve_by_elim},
  inf := λ S₁ S₂, ⟨S₁.val ∩ S₂.val, by {apply is_regular_inter, from S₁.property, from S₂.property}⟩,
  inf_le_left :=
    begin
      intros a b, intros x Hx, from Hx.left
    end,
  inf_le_right :=
    begin
      intros a b, intros x Hx, from Hx.right
    end,
  le_inf :=
    begin
      intros a b c H₁ H₂, intros x Hx, split; solve_by_elim
    end,
  ..regular_open_poset}
local attribute [instance] regular_open_lattice

def regular_open_bounded_lattice : bounded_lattice (regular_opens α) :=
{  top := ⟨set.univ, is_regular_univ⟩,
  le_top := by tidy,
  bot := ⟨∅, is_regular_empty⟩,
  bot_le := by tidy,
 .. regular_open_lattice}

local attribute [instance] regular_open_bounded_lattice

def regular_open.neg : (regular_opens α) → (regular_opens α) := λ x, ⟨xᵖ, by {rw[regular_iff_p_p], symmetry, apply p_eq_p_p_p,
                       from is_open_of_is_regular x.property}⟩

def regular_open_has_neg : has_neg (regular_opens α) :=
⟨regular_open.neg⟩
local attribute [instance] regular_open_has_neg


def regular_open.Sup : set (regular_opens α) → (regular_opens α) :=
λ 𝒮, ⟨⋃₀(subtype.val '' 𝒮)ᵖᵖ, is_regular_p_p⟩

def regular_open_has_Sup : has_Sup (regular_opens α) :=
⟨regular_open.Sup⟩
local attribute [instance] regular_open_has_Sup

lemma Sup_unfold {𝒜 : set (regular_opens α)} : Sup 𝒜 = regular_open.Sup 𝒜 := rfl

lemma regular_open_le_Sup :
  ∀ (s : set (regular_opens α)) (a : {S // is_regular S}), a ∈ s → a ≤ has_Sup.Sup s :=
begin
  intros s a Ha, intros x Hx, unfold has_Sup.Sup regular_open.Sup,
  simp, suffices : x ∈ (⋃ (x : {S // is_regular S}) (H : x ∈ s), x.val),
  apply subset_int_cl_of_open, {apply is_open_Union, intros, apply is_open_Union,
  intros, from is_open_of_is_regular i.property},
  simp, use a, tidy, recover
end

lemma regular_open_Sup_le :
∀ (s : set (regular_opens α)) (a : {S // is_regular S}),
    (∀ (b : {S // is_regular S}), b ∈ s → b ≤ a) → has_Sup.Sup s ≤ a :=
begin
  intros 𝒜 A H,
    unfold has_Sup.Sup regular_open_has_Sup regular_open.Sup, simp,
    suffices : (⋃ (x : {S // is_regular S}) (H : x ∈ 𝒜), x.val)ᵖᵖ ⊆ A.val,
      by tidy,
    apply is_regular_stable_subset, from A.property, tidy
end

lemma perp_self_empty {S : set α} : S ∩ (Sᵖ) = ∅ :=
by tidy

lemma inf_unfold {x₁ x₂ : (regular_opens α)} : (x₁ ⊓ x₂) = ⟨x₁.val ∩ x₂.val, is_regular_inter x₁.property x₂.property⟩ :=
by refl
local attribute [simp, priority 0] inf_unfold

lemma neg_unfold {x : (regular_opens α)} : (- x) = ⟨xᵖ, by {rw[regular_iff_p_p], symmetry, apply p_eq_p_p_p,
                       from is_open_of_is_regular x.property}⟩ := by refl

local attribute [simp, priority 0] neg_unfold

@[simp]lemma neg_neg_eq_self {x : (regular_opens α)} : - - x = x :=
begin
  simp, apply subtype.eq, simp, apply is_regular_eq_p_p, from x.property
end
local attribute [simp] neg_neg_eq_self

lemma sup_unfold {x₁ x₂ : (regular_opens α)} :
  (x₁ ⊔ x₂) = ⟨(x₁.val ∪ x₂.val)ᵖᵖ, by {apply is_regular_sup}⟩ := by refl
local attribute [simp, priority 0] sup_unfold

lemma top_unfold : (⊤ : (regular_opens α)).val = set.univ := rfl
local attribute [simp, priority 0] top_unfold

lemma regular_open_inf_neg_eq_bot : ∀ (x : (regular_opens α)), x ⊓ -x = ⊥ :=
by {tidy, suffices : x_val ∩ (x_valᵖ) = (⊥ : (regular_opens α)).val, apply subtype.eq,
   from this, from perp_self_empty}

lemma regular_open_sup_neg_eq_top : ∀ (x : (regular_opens α)), x ⊔ -x = ⊤ :=
begin
  intro x, apply subtype.eq, simp, ext, split; intros, trivial,
    tidy, unfold is_regular at x_property, rw[<-x_property] at a_1,
    suffices : cl x_val ∪ - x_val = univ,
      {rw[this] at a_1, apply a_1, simp},
    tidy, by_cases x ∈ x_val,
      left, from subset_closure h,
      right, from ‹_›
end

def regular_open_boolean_algebra : boolean_algebra (regular_opens α) :=
{le_sup_inf :=
    begin
      intros x y z,
        intros a Ha, simp only [inf_unfold, sup_unfold] at Ha ⊢,
        rw[<-p_p_inter_eq_inter_p_p] at Ha,
        suffices : (x.val ∪ y.val) ∩ (x.val ∪ z.val) ⊆ x.val ∪ y.val ∩ z.val,
          by {apply p_p_mono; from ‹_›},
        simp only [inter_distrib_left, inter_distrib_right],
        tactic.rotate 1,
        from is_open_union (is_open_of_is_regular x.property) (is_open_of_is_regular y.property),
        from is_open_union (is_open_of_is_regular x.property) (is_open_of_is_regular z.property),
        /- `tidy` says -/ intros a_1 a_2, cases a_2, cases z, cases y, cases x,
        work_on_goal 0 { cases a_2, work_on_goal 0 { cases a_2, dsimp at *, simp at *,
        cases Ha, cases Ha_h, cases Ha_h_w, cc },
          cases a_2, dsimp at *, simp at *, cases Ha, cases Ha_h, cases Ha_h_w, cc },
        cases a_2, cases z, cases y, cases x,
        work_on_goal 0 { cases a_2, dsimp at *, simp at *, cases Ha, cases Ha_h, cases Ha_h_w, cc },
        cases a_2, cases z, cases y, cases x, dsimp at *, simp at *,
        cases Ha, cases Ha_h, cases Ha_h_w, cc
    end,
  sub := λ A B, A ⊓ (-B),
  inf_neg_eq_bot := regular_open_inf_neg_eq_bot,
  sup_neg_eq_top := regular_open_sup_neg_eq_top,
  sub_eq := by {intros x y, refl},
  .. regular_open_has_neg,
  .. regular_open_bounded_lattice
}

local attribute [instance] regular_open_boolean_algebra

def regular_open_has_Inf : has_Inf (regular_opens α) :=
{ Inf := λ 𝒮, ⟨regular_open.neg ((Sup) ((λ x : (regular_opens α), -x) '' 𝒮)),
begin
  rw[regular_iff_p_p], change (_)ᵖᵖᵖ = (_)ᵖ, symmetry,
      apply p_eq_p_p_p, rw[Sup_unfold], simp[regular_open.Sup]
end⟩ }
local attribute [instance] regular_open_has_Inf

include α
@[simp]lemma Inf_unfold : ∀ s : set (regular_opens α), Inf s = - Sup ((λ x, - x) '' s) :=
by tidy

lemma regular_open_Inf_le : ∀s : set (regular_opens α), ∀a ∈ s, Inf s ≤ a :=
begin
  intros 𝒜 A H_mem,
  rw[show A = - - A, from (lattice.neg_neg).symm],
  have := lattice.neg_le_neg _,
  convert this, apply regular_open_le_Sup, use A, tidy
end

lemma regular_open_le_Inf : ∀(s : set (regular_opens α)) a, (∀b∈s, a ≤ b) → a ≤ Inf s :=
begin
  intros 𝒜 A H_mme, rw[show A = - - A, from (lattice.neg_neg).symm],
  rw[Inf_unfold], apply lattice.neg_le_neg _,
  have := regular_open_Sup_le _ _ _,
  convert this, intros, specialize H_mme (-b),
  simp[-neg_unfold] at a,
  rcases a with ⟨w,⟨h₁,⟨h₂,h₃⟩⟩⟩,
    suffices : A ≤ -b,
      replace this := lattice.neg_le_neg this,
      convert this, symmetry, apply neg_neg_eq_self,
      replace h₃ := (congr_arg (λ x, - x) h₃).symm,
      dsimp at h₃, simp only [h₃] at *,
      apply H_mme, simp*
end

def regular_open_complete_lattice : complete_lattice (regular_opens α) :=
{le_Sup := regular_open_le_Sup,
  Sup_le := regular_open_Sup_le,
  Inf_le := regular_open_Inf_le,
  le_Inf := regular_open_le_Inf,
  .. regular_open_boolean_algebra,
  .. regular_open_has_Inf,
  .. regular_open_has_Sup,
  .. regular_open_has_neg,
  .. regular_open_bounded_lattice}

local attribute [instance] regular_open_complete_lattice

lemma regular_open_inf_Sup_le_supr_inf : ∀(a : (regular_opens α)) s, a ⊓ Sup s ≤ (⨆ b ∈ s, a ⊓ b) :=
begin
  letI : complete_lattice (regular_opens α) := by apply_instance,
  intros A 𝒜, rw[inf_comm], rw[deduction], let X := _, change _ ≤ X, have := Sup_le, show Type u_1, from (regular_opens α),
  show complete_lattice _, dsimp, apply_instance, dsimp at this,
  tactic.rotate 2, from X, apply this, dsimp[X], intros B H_B, rw[<-deduction],
  rw[inf_comm], have := le_supr_of_le, tactic.rotate 1, from (regular_opens α), tactic.rotate 1,
  apply_instance, from λ (b : subtype is_regular), ⨆(H : b ∈ 𝒜), A ⊓ b, from A ⊓ B,
  specialize this B, apply this, have := @le_supr_of_le (regular_opens α) (B ∈ 𝒜) _,
  apply this, from ‹_›, apply regular_open_poset.le_refl
end

lemma shift_neg_right {a b : (regular_opens α)} (h : a = -b) : -a = b :=
by {rw[h], from lattice.neg_neg}

-- variables {α : Type*} [τ : topological_space α]

-- local postfix `ᵖ`:80 := perp

-- local notation `cl`:65 := closure

-- local notation `int`:65 := interior

-- include τ
lemma regular_open_infi_sup_le_sup_Inf : ∀(a : (regular_opens α)) s, (⨅ b ∈ s, a ⊔ b) ≤ a ⊔ Inf s :=
begin
  intros A 𝒜,
  have : A ⊔ Inf 𝒜 = -(-A ⊓ -(Inf 𝒜)),
    by {symmetry, apply shift_neg_right, rw[neg_sup]},
  rw[this], apply @neg_le_neg' ((regular_opens α)) _,
  unfold infi,
  simp only[Inf_unfold], have this₁ := @lattice.neg_neg (regular_opens α) _ _,
  rw[this₁], have this₂ := @lattice.neg_neg (regular_opens α) _ _, rw[this₂],
  have this' := @le_trans (regular_opens α) _,
  have := @regular_open_inf_Sup_le_supr_inf α _ (-A) (has_neg.neg '' 𝒜),
  have this_le := @le_trans (regular_opens α) _, specialize this_le this,
  swap, from Sup
      (has_neg.neg '' range (λ (b : {S // is_regular S}), -Sup (has_neg.neg '' range (λ (H : b ∈ 𝒜), A ⊔ b)))),
  rw[inf_comm], rw[deduction], have := @Sup_le (regular_opens α) _ (has_neg.neg '' 𝒜),
  let X := _, change _ ≤ X, specialize @this X, apply this, intros b Hb, dsimp[X], rw[<-deduction, inf_comm],
  clear this_le, simp only [mem_image] at Hb, cases Hb with b' Hb', rcases Hb' with ⟨H'', ⟨Hb''₁, Hb''₂⟩⟩,
  change -A ⊓ -(b') ≤ _,
  have : -A ⊓ (-b') = -(A ⊔ b'), by {rw[<-neg_sup]}, rw[this],
  have := @le_Sup (regular_opens α) _ (has_neg.neg '' range (λ (b : subtype is_regular), -Sup (has_neg.neg '' range (λ (H : b ∈ 𝒜), A ⊔ b)))),
  apply this, simp only [mem_image],
  use (A ⊔ b'), split, apply mem_range.mpr,
  use b', apply shift_neg_right, clear this,
  apply le_antisymm,
  apply @Sup_le (regular_opens α) _ (has_neg.neg '' range (λ (H : b' ∈ 𝒜), A ⊔ b')) (-(A ⊔ b')),
  intros b'' Hb'',
  simp at Hb'', rcases Hb'' with ⟨w, ⟨⟨Hw₁, Hw₂⟩, ⟨Hw₃, Hw₄⟩⟩⟩,
    rw[<-Hw₄], replace Hw₂ := (congr_arg perp Hw₂).symm,
    simp only [Hw₂], apply le_of_eq _, refl,

  apply @le_Sup (regular_opens α) _ (has_neg.neg '' range (λ (H : b' ∈ 𝒜), A ⊔ b')), simp only [mem_range, mem_image], use (A ⊔ b'), use H'',
  refl, refl
end

def regular_open_algebra (H_nonempty : nonempty α) :
  nontrivial_complete_boolean_algebra (regular_opens α) :=
{infi_sup_le_sup_Inf := regular_open_infi_sup_le_sup_Inf,
  inf_Sup_le_supr_inf := regular_open_inf_Sup_le_supr_inf,
  bot_lt_top :=
    by {apply lt_iff_le_and_ne.mpr, split,
       have := regular_open_bounded_lattice.bot_le, specialize this ⊤,
       from this, intro H, simp[subtype.ext] at H,
       change (∅ : set α) = univ at H, tactic.unfreeze_local_instances,
       cases H_nonempty, suffices : H_nonempty ∈ (∅ : set α), by {cases this}, simp[H]},
  .. regular_open_boolean_algebra,
  ..regular_open_complete_lattice
  }

lemma p_p_eq_univ_of_dense {S : set α} (H_dense : dense S) : Sᵖᵖ = univ :=
by simp only [perp_unfold, closure_univ_of_dense H_dense,
               set.compl_univ, closure_empty, set.compl_empty]

lemma Sup_eq_top_of_dense_Union {ι} {rO : ι → regular_opens α}
  (H_dense : dense $ ⋃₀(subtype.val '' range (λ (i : ι), rO i)))
  : (⨆i, rO i : regular_opens α) = ⊤ :=
by {change Sup _ = _, rw[Sup_unfold], exact subtype.ext.mpr (p_p_eq_univ_of_dense ‹_›)}

open cardinal function
local attribute [instance] [priority 0] subtype.preorder

lemma CCC_regular_opens (h : countable_chain_condition α) : CCC (regular_opens α) :=
begin
  intros β O hO h2O,
  have O_inj : injective (subtype.val ∘ O),
  { apply injective_comp subtype.val_injective, intros x y hxy,
    by_contra, apply not_le_of_gt (hO y),
    have := h2O _ _ a, rwa [hxy, inf_self] at this },
  have := h (range (subtype.val ∘ O)) _ _,
  rw [countable_iff] at this, convert this using 1,
  { rw [mk_range_eq], exact O_inj },
  { rintro _ ⟨x, rfl⟩, exact is_open_of_is_regular (O x).2 },
  { rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy,
    have : x ≠ y, { intro h, apply hxy, exact congr_arg (subtype.val ∘ O) h },
    rw [disjoint_iff_eq_empty], refine subset.antisymm _ (empty_subset _), exact h2O _ _ this }
end

end regular_algebra
