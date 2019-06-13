import .bvm .bvm_extras .regular_open_algebra .to_mathlib

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

section collapse_poset
variables (X Y : Type u)
/--
A member of `collapse_poset X Y` is an "indexed" partial function from a countable subset of X into Y.
-/
structure collapse_poset :=
(dom      : ℕ → X)
(im       : ℕ → Y)
(congr    : ∀ k₁ k₂ : ℕ, dom k₁ = dom k₂ → im k₁ = im k₂)
-- (inj : function.injective dom) -- TODO(jesse) do we need to also assume this?

variables {X Y}
def collapse_poset.extends (p : collapse_poset X Y) (f : X → Y) : Prop :=
∀ k : ℕ, f(p.dom k) = p.im k

/--
The basic open attached to (p : collapse_poset X Y) is the collection of all functions g which extend p.
-/
def collapse_poset.principal_open (p : collapse_poset X Y) : set (X → Y) :=
{g | collapse_poset.extends p g}

-- -- @[instance, priority 9001]
-- def collapse_space (X Y) : topological_space (X → Y) :=
-- generate_from _ 
end collapse_poset

@[instance, priority 9001]def collapse_space (X Y : Type u) : topological_space (X → Y) :=
generate_from $ collapse_poset.principal_open '' set.univ

lemma collapse_poset.principal_open_is_open {X Y} {p : collapse_poset X Y} : is_open (collapse_poset.principal_open p) :=
by {constructor, use p, simp}

lemma collapse_poset.principal_open_is_closed {X Y} {p : collapse_poset X Y} : is_closed (collapse_poset.principal_open p) := sorry

lemma collapse_poset.principal_open_is_clopen {X Y} {p : collapse_poset X Y} : is_clopen (collapse_poset.principal_open p) :=
⟨collapse_poset.principal_open_is_open, collapse_poset.principal_open_is_closed⟩ 

section collapsing_algebra
variables (X Y : Type u)

local notation `ノಠ益ಠ)ノ彡┻━┻`:50 := collapse_poset.principal_open
/--
  The collapse algebra of X and Y is the algebra of regular opens of the collapse space of X and Y.
-/
def collapse_algebra := @regular_opens (X → Y) (collapse_space X Y)

-- end collapsing_algebra

-- section collapsing_algebra
variables {X Y}
variable [H_nonempty : nonempty (X → Y)]

-- @[instance, priority 9001]def collapse_algebra_is_boolean_algebra [H_nonempty : nonempty Y] : nontrivial_complete_boolean_algebra (collapse_algebra X Y) :=
-- begin
--   suffices this : nonempty (X → Y),
--     from regular_open_algebra ‹_›,
--   from ⟨λ _, classical.choice ‹_›⟩
-- end

@[instance, priority 10000]def complete_boolean_algebra_collapse_algebra : nontrivial_complete_boolean_algebra (collapse_algebra X Y) :=
regular_open_algebra H_nonempty

def collapse_poset.canonical_inclusion : collapse_poset X Y → collapse_algebra X Y :=
λ p, ⟨ノಠ益ಠ)ノ彡┻━┻ p, is_regular_of_clopen collapse_poset.principal_open_is_clopen⟩


notation `⟨ﾉ◕ヮ◕⟩ﾉ`:100 := collapse_poset.canonical_inclusion

-- ち ぢ っ つ づ て で と ど な に ぬ ね の は

include H_nonempty
lemma collapse_poset_dense {b : collapse_algebra X Y} (H : ⊥ ≤ b) : ∃ p, ⟨ﾉ◕ヮ◕⟩ﾉ p ≤ b := sorry

-- #check (by apply_instance : has_le (X → Y))




-- instance discrete_topology_continuum : topological_space (set ℕ) := generate_from ⊤

-- /-- the Boolean algebra for forcing CH is the regular open algebra of the space of functions {ℵ₁ → set(ω)}, where both ℵ₁ and (set(ω)) are given the discrete topology -/
-- def collapsing_algebra : Type* :=
--   @regular_opens (card_ex (aleph 1) → (set ℕ)) (Pi.topological_space)

/-
Now, we need a surjection to appear, so that (in V 𝔹) ℵ₁ ↠ 𝒫(ω). This means that ℵ₁ is larger than 𝒫(ω), so that ¬ (ℵ₁ < 𝒫(ω)).

Since ω < 𝒫(ω) is absolute (I think), we just need that 𝒫(ω) ≤ ℵ₁, so we need to construct an injection.

Anyways, here's the goal: to show that 𝒫(ω) is the same size as ℵ₁, we need to exhibit an injection into 𝒫(ω),

and we need to exhibit an injection 𝒫(ω) ↪ ℵ₁, and then the result should follow from Schroeder-Bernstein.

Alternately, we can try to construct surjections going either way, which should prove that the sets are equinumerous.
-/

/-
  Note: Proposition 14.2 says that once we complete a σ-closed forcing, it we can show that

For any P-name f such that there exists p : P with p ⊩ (f is a function with domain ω), there exists a q ≤ p and a real function g such that q ⊩ f = ǧ.

In either case, we will have to show that the canonical comparison maps

ℵ₁ → ℵ₁̌, and P(ω) → P(ω)̌  are surjective. This has a very clear meaning for the powerset of omega, less so for aleph 1, but I think if we grind out the calculations we will see.
-/

/- 2019-06-12T14:21:36

Note that by some considerations in Chapter 2 of Bell, we have that

⊤ ≤ (ℵ_η)̌  ≤ (ℵ_(η̌)) (by a well-founded recursion)

We furthermore then need that, assuming we have a σ-closed forcing, that

⊤ ≤ (ℵ_(η̌)) ≤ (ℵ_η)̌ , because otherwise, (ℵ_η)̌  < ℵ_(η̌) and therefore, (ℵ_η)̌  is countable. But this contradicts the fact that these maps must be reflected back to pSet.
-/

end collapsing_algebra

variables (X Y : Type u) [H_nonempty : nonempty (X → Y)]
local notation `𝔹` := (collapse_algebra X Y)

#exit
include H_nonempty
def function_reflect (x y : pSet) (Γ : 𝔹) (f) (H : Γ ≤ is_func' (x̌) (y̌) f) : pSet := sorry

def function_reflect_spec (x y : pSet} (Γ : 𝔹) (f) (H : Γ ≤ is_func' (x̌) (y̌) f) : (function_reflect x y Γ f H)̌  =ᴮ f := sorry




