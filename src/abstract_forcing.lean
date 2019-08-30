/- The formalism of forcing, following Justin Moore's notes -/

import order.bounded_lattice tactic order.complete_boolean_algebra set_theory.zfc .to_mathlib

open lattice

universe u

@[class]def forcing_notion (α : Type u) : Type u := order_top α

-- @[instance]def has_top_forcing_notion (α : Type u) [H : forcing_notion α] : has_top α := sorry

instance partial_order_of_forcing_notion (α : Type u) [H : forcing_notion α] : partial_order α :=
{ le := H.le,
  lt := H.lt,
  le_refl := H.le_refl,
  le_trans := H.le_trans,
  lt_iff_le_not_le := H.lt_iff_le_not_le,
  le_antisymm := H.le_antisymm }

def order_top.mk {α : Type u} [H₁ : partial_order α] [H₂ : has_top α] (H : ∀ a : α, a ≤ ⊤) : order_top α :=
{ top := ⊤,
  le := (≤),
  lt := (<),
  le_refl := H₁.le_refl,
  le_trans := H₁.le_trans,
  lt_iff_le_not_le := H₁.lt_iff_le_not_le,
  le_antisymm := H₁.le_antisymm,
  le_top := H }

@[instance]example {α : Type u} : forcing_notion (set α) :=
order_top.mk (λ _, le_top)

/- A pfilter is an order-theoretic filter on the partial order α  -/
structure pfilter (α : Type u) [partial_order α] : Type u :=
(X : set α)
(nonempty : X ≠ ∅)
(upward_closed : ∀ (p q : α) (H_le : p ≤ q) (H_mem : p ∈ X), q ∈ X)
(downward_directed : ∀ (p q ∈ X), ∃ r ∈ X, r ≤ p ∧ r ≤ q)

inductive Name (P : Type u) [forcing_notion P] : Type (u+1)
| mk (α : Type u) (A : α → Name) (B : α → P) : Name

postfix `-name`:100 := Name

instance : partial_order punit :=
{ le := λ _ _, true,
  lt := λ _ _, false,
  le_refl := by simp,
  le_trans := by simp,
  lt_iff_le_not_le := by simp,
  le_antisymm := by finish }

instance : has_top punit := ⟨punit.star⟩

instance : forcing_notion punit := order_top.mk (by finish)

instance forcing_notion_complete_boolean_algebra {α : Type u} [complete_boolean_algebra α] : forcing_notion α := order_top.mk (by finish)

--TODO(jesse) rewrite in terms of pSet.rec and Name.rec
def pSet_equiv_trivial_name : pSet.{u} ≃ (punit-name : Type (u+1)) :=
{ to_fun := λ u,
  begin
    induction u with α A ih,
    from ⟨α, ih, λ _, punit.star⟩
  end,
  inv_fun := λ v,
  begin
    induction v with α A B ih,
    from ⟨α, ih⟩
  end,
  left_inv :=
    λ x, by induction x; finish,
  right_inv :=
    λ y, by induction y; finish }

-- def Pcheck {P} [forcing_notion P] : pSet.{u} → (P-name : Type (u+1))
-- | ⟨α, A⟩ := ⟨α, λ a, Pcheck (A a), λ _, ⊤⟩


namespace pfilter

-- note: this will require a smallness argument, since we're going to be reconstructing a type in the ground model

/-
from Moore's "The method of forcing":

If G is any filter and ẋ is any Q-name, define
ẋ(G) recursively by ẋ(G) := { ẏ(G) : ∃p ∈ G (( ẏ, p) ∈ ẋ)}

x ↦ ẋ is a map (Name α).{u} → Type u, parametrized by a pfilter (G : pfilter α)

However, what does it mean for a filter in this case to be generic?
-/
def eval {P : Type u} [forcing_notion P] (𝒢 : pfilter P) : P-name → Type u
| ⟨α, A, B⟩ := Σ p : {a : α // B a ∈ 𝒢.X}, eval (A p.1)

def eval_image {P : Type u} [forcing_notion P] (𝒢 : pfilter P): Type (u + 1) :=
{α // ∃ x, α = eval 𝒢 x} -- this should be our new model of set theory

--TODO 6.8. 6.9, and 6.10 from Moore's notes

-- def foo {P : Type u} [forcing_notion P] (𝒢 : pfilter P)  : pSet.{u} → (eval_image.{u} 𝒢) := λ x, ⟨eval 𝒢 (Pcheck x), ⟨_, rfl⟩⟩

-- now foo is the canonical map from pSet to eval_image
-- need to check that (foo x) is "equivalent" to x again in some way

end pfilter
