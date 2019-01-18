import .fol set_theory.zfc data.pfun data.set tactic.tidy data.set.countable

open fol

/- The Cohen poset of finite partial functions ω → 2 -/

/- The underlying type of the Cohen poset is the type of finite partial functions from ω → 2-/
def cohen_poset := {f : ℕ →. bool | set.finite (pfun.dom f)}

/- Two partial functions are equal if their graphs are equal -/
lemma ext_graph {α β : Type*} (f g : α →. β) (h_graph : f.graph = g.graph) : f = g :=
pfun.ext $ λ a b, iff_of_eq (congr_fun h_graph (a,b))

/- Partial order structure on the Cohen poset -/
instance partial_order_cohen_poset : partial_order cohen_poset :=
{ le := λ f g, g.val.graph ⊆ f.val.graph,
  lt := λ f g, g.val.graph ⊆ f.val.graph ∧ ¬ f.val.graph ⊆ g.val.graph,
  le_refl := λ _, by unfold has_le.le,
  le_trans := by {intros, apply set.subset.trans, exact a_2, assumption},
  lt_iff_le_not_le := λ _ _, iff.refl _,
  le_antisymm := λ a b h1 h2, by {have := @set.subset.antisymm _ _ _ h2 h1, cases a, cases b,
                                       congr, apply ext_graph, exact this}}

def incompatible {α : Type*} [partial_order α] (a b : α) := ¬ ∃ c, c ≤ a ∧ c ≤ b

def antichain {α : Type*} [partial_order α] (s : set α) := ∀ x ∈ s, ∀ y ∈ s, incompatible x y

def countable_chain_condition (α : Type*) [partial_order α] := ∀ s : set α, antichain s → set.countable s

lemma cohen_poset_ccc : countable_chain_condition cohen_poset :=
  sorry
