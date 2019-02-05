import fol set_theory.zfc order.boolean_algebra order.complete_boolean_algebra

open lattice

universe u

variables (β : Type u) [complete_boolean_algebra β]

lemma forall_and {α : Type*} {p q : α → Prop} : (∀ x, p x) ∧ (∀ y, q y) ↔ ∀ x, p x ∧ q x :=
  by finish

-- τ is a B-name if and only if τ is a set of pairs of the form ⟨σ, b⟩, where σ is
-- a B-name and b ∈ B.
inductive B_name : Type (u+1)
| mk (α : Type u) (A : α → B_name) (B : α → β) : B_name

instance nonempty_B_name : nonempty $ @B_name β _ := begin apply nonempty.intro, refine ⟨_,_,_⟩, exact ulift empty, intro x, repeat{cases x}, intro x, repeat{cases x} end

def preempty : B_name β :=
begin refine ⟨_,_,_⟩, exact ulift empty, intro x, repeat{cases x}, intro x, repeat{cases x} end

/-- Two Boolean-valued pre-sets are extensionally equivalent if every
  element of the first family is extensionally equivalent to
  some element of the second family and vice-versa. -/
def bool_equiv : ∀ (x y : B_name β), β
/- ∀ x ∃ y, m x y ∧ ∀ y ∃ x, m y x, but this time in ~lattice~ -/
| (B_name.mk α A B) (B_name.mk α' A' B') := (infi $ (λ a : α, supr $ λ a', bool_equiv (A a) (A' a'))) ⊓ (infi $ λ a', supr $ λ a, bool_equiv (A a) (A' a'))

theorem bool_equiv_refl_empty : (bool_equiv β) (preempty β) (preempty β) = ⊤ :=
  by unfold preempty bool_equiv;
  {simp only [lattice.inf_eq_top_iff, lattice.infi_eq_top], fsplit; intros i; cases i; cases i}

open lattice

theorem bool_equiv_refl : ∀(x), bool_equiv β x x = ⊤ :=
by intro x; induction x; simp[bool_equiv]; split; intros;
  from (top_unique $ le_supr_of_le i $ by rwa[x_ih i])

