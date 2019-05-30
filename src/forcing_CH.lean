import .bvm .bvm_extras .regular_open_algebra

/-
  Forcing the continuum hypothesis.
-/

universe u

open lattice bSet topological_space pSet cardinal

section lemmas

variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

/-- Corresponds to proposition 5.2 in Moore's 'the method of forcing':
Let x be a set and let ϕ(v) be a formula in the forcing language. If ∀ y ∈ x, p ⊩ ϕ(y̌), then p ⊩ ∀ y ∈ (x̌), ϕ(y)
-/
lemma check_forall (x : pSet) (ϕ : bSet 𝔹 → 𝔹) {h : B_ext ϕ} {b : 𝔹} :
  (∀ (y : x.type), b ≤ ϕ((x.func y)̌ )) → (b ≤ (⨅(y : x.type), ϕ((x.func y)̌ ))) := λ H, le_infi ‹_›

end lemmas

section collapsing_algebra

instance discrete_topology_continuum : topological_space (set ℕ) := generate_from ⊤

/-- the Boolean algebra for forcing CH is the regular open algebra of the space of functions {ℵ₁ → set(ω)}, where both ℵ₁ and (set(ω)) are given the discrete topology -/
def collapsing_algebra : Type* :=
  @regular_opens (card_ex (aleph 1) → (set ℕ)) (Pi.topological_space)

/-
Now, we need a surjection to appear, so that (in V 𝔹) ℵ₁ ↠ 𝒫(ω). This means that ℵ₁ is larger than 𝒫(ω), so that ¬ (ℵ₁ < 𝒫(ω)).

Since ω < 𝒫(ω) is absolute (I think), we just need that 𝒫(ω) ≤ ℵ₁, so we need to construct an injection.

Anyways, here's the goal: to show that 𝒫(ω) is the same size as ℵ₁, we need to exhibit an injection into 𝒫(ω),

and we need to exhibit an injection 𝒫(ω) ↪ ℵ₁, and then the result should follow from Schroeder-Bernstein.

Alternately, we can try to construct surjections going either way, which should prove that the sets are equinumerous.
-/

end collapsing_algebra
