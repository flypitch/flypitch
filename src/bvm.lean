import fol set_theory.zfc order.boolean_algebra order.complete_boolean_algebra .cohen_poset

open lattice

universe u

/- A β-valued model of ZFC -/

namespace lattice
def imp {α : Type*} [boolean_algebra α] : α → α → α :=
  λ a₁ a₂, (- a₁) ⊔ a₂

infix ` ⟹ `:50 := lattice.imp

lemma imp_neg_sub {α : Type*} [boolean_algebra α] {a₁ a₂ : α} :  -(a₁ ⟹ a₂) = a₁ - a₂ :=
  by {rw[sub_eq, imp]; finish}

lemma inf_eq_of_le {α : Type*} [distrib_lattice α] {a b : α} (h : a ≤ b) : a ⊓ b = a :=
  by apply le_antisymm; finish[le_inf]

/-- the deduction theorem in β -/
@[simp]lemma imp_top_iff_le {α : Type*} [boolean_algebra α] {a₁ a₂ : α} : (a₁ ⟹ a₂ = ⊤) ↔ a₁ ≤ a₂ :=
begin
 split; intro H,
  {have : a₁ ⊓ a₂ = a₁, from
    calc a₁ ⊓ a₂ = ⊥ ⊔ (a₁ ⊓ a₂) : by simp
             ... = (a₁ ⊓ - a₁) ⊔ (a₁ ⊓ a₂) : by simp
             ... = a₁ ⊓ (- a₁ ⊔ a₂) : by {rw[inf_sup_left]}
             ... = a₁ ⊓ ⊤ : by {rw[<-H], refl}
             ... = a₁ : by {simp},
             
   finish},
 {have : a₁ ⊓ a₂ = a₁, from inf_eq_of_le H, apply top_unique,
  have this' : ⊤ = - a₁ ⊔ a₁, by rw[lattice.neg_sup_eq_top],
  rw[this', <-this, imp], simp only [lattice.neg_inf, lattice.sup_le_iff],
  repeat{split},
    suffices : (- a₁ ≤ - a₁ ⊔ - a₂ ⊔ a₂) = (- a₁ ≤ - a₁ ⊔ (- a₂ ⊔ a₂)),
      by rw[this]; apply le_sup_left, ac_refl,
    suffices : (-a₂ ≤ -a₁ ⊔ -a₂ ⊔ a₂) = (- a₂ ≤ - a₂ ⊔ (-a₁ ⊔ a₂)),
      by rw[this]; apply le_sup_left, ac_refl,
    suffices : - a₁ ⊔ - a₂ ⊔ a₂ = ⊤,
      by rw[this]; simp, apply top_unique,
      suffices : - a₁ ⊔ - a₂ ⊔ a₂ = - a₁ ⊔ (- a₂ ⊔ a₂),
        by simp[this], ac_refl}
end
end lattice


namespace bSet

-- note: use forall_and_distrib in core, which is the same statement but with the ↔ reversed

-- lemma forall_and {α : Type*} {p q : α → Prop} : (∀ x, p x) ∧ (∀ y, q y) ↔ ∀ x, p x ∧ q x :=
--   by finish

-- τ is a B-name if and only if τ is a set of pairs of the form ⟨σ, b⟩, where σ is
-- a B-name and b ∈ B.
inductive B_name (β : Type u) [complete_boolean_algebra β] : Type (u+1)
| mk (α : Type u) (A : α → B_name) (B : α → β) : B_name

export B_name

variables {β : Type u} [complete_boolean_algebra β]

def empty : B_name β :=
  ⟨ulift empty, empty.elim ∘ ulift.down, empty.elim ∘ ulift.down⟩

instance nonempty_B_name : nonempty $ @B_name β _ :=
  ⟨empty⟩

instance has_empty_bSet : has_emptyc (B_name β) := ⟨empty⟩

/-- Two Boolean-valued pre-sets are extensionally equivalent if every
  element of the first family is extensionally equivalent to
  some element of the second family and vice-versa. -/
def bool_equiv : ∀ (x y : B_name β), β
/- ∀ x ∃ y, m x y ∧ ∀ y ∃ x, m y x, but this time in ~lattice~ -/
| (mk α A B) (mk α' A' B') :=
             (⨅a : α, B a ⟹ ⨆a', B' a' ⊓ bool_equiv (A a) (A' a')) ⊓
               (⨅a' : α', B' a' ⟹ ⨆a, B a ⊓ bool_equiv (A a) (A' a'))


infix ` =ᴮ `:80 := bool_equiv

theorem bool_equiv_refl_empty : (@bool_equiv β _) (empty) (empty) = ⊤ :=
  by unfold empty bool_equiv;
  {simp only [lattice.inf_eq_top_iff, lattice.infi_eq_top], fsplit; intros i; cases i; cases i}

open lattice

@[simp]theorem bool_equiv_refl : ∀ x, @bool_equiv β _ x x = ⊤ :=
begin
  intro x, induction x, simp[bool_equiv, -imp_top_iff_le], split; intros;
  {apply top_unique, simp, apply le_supr_of_le i, have := x_ih i, finish}
end

/- empty' is the singleton B_name {⟨∅, ⊥⟩}, i.e. a set whose only member is ∅ which has
   a zero probability of actually being an element. It should be equivalent to ∅. -/
def empty' : B_name β := mk punit (λ _, ∅) (λ _, ⊥)

example : empty =ᴮ empty = (⊤ : β) :=
  by tidy

/-- `x ∈ y` as Boolean-valued pre-sets if `x` is extensionally equivalent to a member
  of the family `y`. -/
def mem : B_name β → B_name β → β
| a (mk α' A' B') := ⨆a', B' a' ⊓ a =ᴮ A' a'

def empty'' : B_name β :=
  mk (ulift bool) (λ x, ∅) (λ x, by {repeat{cases x}, exact ⊥, exact ⊤})

infix ` ∈ᴮ `:80 := mem

/-- ∅ appears in empty'' with probability 0 and 1, with the higher probability winning the
    vote of membership. This demonstrates why the inequality in the following theorem is
    necessary. -/
example : ∅ ∈ᴮ empty'' = (⊤ : β) :=
  by {apply top_unique, apply le_supr_of_le ⊤, swap, exact ⟨⟨(tt)⟩⟩, finish}

theorem mem.mk {α : Type*} (A : α → B_name β) (B : α → β) (a : α) : A a ∈ᴮ mk α A B ≥ B a :=
  le_supr_of_le a $ by simp

protected def subset : B_name β → B_name β → β
| (mk α A B) b := ⨅a:α, B a ⟹ (A a ∈ᴮ b)

/-- Mixing lemma, c.f. Bell's book or Lemma 1 of Hamkins-Seabold -/

lemma mixing_lemma {A : set β} (h_anti : antichain A) (τ : A → B_name β) :
  ∃ x, ∀ a : β, a ∈ A → a ≤ x =ᴮ τ ⟨a, by assumption⟩ := sorry

end bSet
