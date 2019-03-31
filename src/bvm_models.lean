import .bvm .bfol .bvm_extras

open lattice

open bSet

open fol

local infix ` ⟹' `:65 := lattice.imp

-- local infix ` ⟹ `:62 := bd_imp

local infix ` ⇔' `:50 := lattice.biimp

-- local infix ` ⇔ `:61 := bd_biimp

section ZFC'
inductive ZFC'_rel : ℕ → Type 1
| ε : ZFC'_rel 2

inductive ZFC'_func : ℕ → Type 1
| emptyset : ZFC'_func 0
| pr : ZFC'_func 2
| ω : ZFC'_func 0
| P_ω : ZFC'_func 0
| Union : ZFC'_func 1

def L_ZFC' : Language.{1} :=
{ functions := ZFC'_func,
  relations := ZFC'_rel }

end ZFC'

variables {𝔹 : Type 0} [nontrivial_complete_boolean_algebra 𝔹]

def bSet_model_fun_map : Π {n : ℕ}, L_ZFC'.functions n → dvector (bSet 𝔹) n → bSet 𝔹 :=
begin
  intros n S,
    induction S,
  from λ _, bSet.empty,
  from λ x, by {cases x, refine bSet.pair x_x _, cases x_xs, from x_xs_x},
  from λ _, bSet.omega,
  from λ _, bv_powerset(omega),
  from λ x, by {cases x, from bv_union ‹_›}
end

def bSet_model_rel_map : Π {n : ℕ}, L_ZFC'.relations n → dvector (bSet 𝔹) n → 𝔹 :=
begin
  intros n R, induction R,
  intro x, cases x, cases x_xs,
  from x_x ∈ᴮ x_xs_x
end

variable (𝔹)
def V : bStructure L_ZFC' (𝔹) :=
{ carrier := (bSet 𝔹),
  fun_map := by apply bSet_model_fun_map,
  rel_map := by apply bSet_model_rel_map,
  eq := bv_eq,
  eq_refl := bv_eq_refl,
  eq_symm := by apply bv_eq_symm,
  eq_trans := by apply bv_eq_trans,
  fun_congr :=
  begin
    intros n F, cases F,
      {intros x y, cases x, cases y, simp},
      tactic.rotate 1,
      {intros x y, cases x, cases y, simp},
      {intros x y, cases x, cases y, simp},
      {intros x y, cases x, cases y, cases x_xs, cases y_xs,
        change (_ ⊓ _ : 𝔹) ≤ (bv_union _) =ᴮ (bv_union _), simp,
        tidy_context, from bv_union_congr ‹_›},
      {intros x y, cases x, cases y, cases x_xs, cases y_xs,
        change (_ ⊓ (_ ⊓ _) : 𝔹) ≤ pair x_x x_xs_x =ᴮ pair y_x y_xs_x,
        cases x_xs_xs, cases y_xs_xs, simp,
        tidy_context, simp[*,pair_congr]}
  end,
  rel_congr :=
  begin
    intros n R, cases R, intros x y,
    cases x, cases y, cases x_xs, cases y_xs,
    cases x_xs_xs, cases y_xs_xs,
    change ((_ ⊓ _) ⊓ (_ ∈ᴮ _) : 𝔹) ≤ (_ ∈ᴮ _), simp,
    tidy_context, apply mem_congr; from ‹_›
  end}


def emptyset {n} : bounded_term L_ZFC' n := bd_const ZFC'_func.emptyset

notation `∅'` := emptyset

def omega {n} : bounded_term L_ZFC' n := bd_const ZFC'_func.ω

notation `ω'` := omega

def P_omega {n} : bounded_term L_ZFC' n := bd_const ZFC'_func.P_ω

notation `P_ω'` := P_omega

def mem {n} (t₁ t₂ : bounded_term L_ZFC' n) : bounded_formula L_ZFC' n :=
@bounded_formula_of_relation L_ZFC' 2 n ZFC'_rel.ε t₁ t₂

local infix ` ∈'`:100 := mem

def pair' {n} (t₁ t₂ : bounded_term L_ZFC' n) : bounded_term L_ZFC' n :=
@bounded_term_of_function L_ZFC' 2 n ZFC'_func.pr t₁ t₂

local prefix `&'`:max := bd_var

-- axiom of extensionality
-- ∀ x y, (∀ z, (z ∈ x → z ∈ y) ∧ (z ∈ y → z ∈ x) → x = y)

def axiom_of_extensionality : sentence L_ZFC' :=
∀' ∀' (∀'(&'0  ∈' &'2 ⇔  &'0 ∈' &'1) ⟹ (&2 ≃ &1))

lemma bSet_models_extensionality : ⊤ ⊩[V 𝔹] axiom_of_extensionality :=
begin
  dsimp [forced_in],
  bv_intro x, bv_intro y,
  simp,
  sorry --bv_intro z, simp[boolean_realize_bounded_formula], sorry, -- need to write simp lemmas saying e.g. boolean_realize_bounded_formula commutes with implication, conjunction, disjunction etc
end

-- axiom of collection
-- For every formula ϕ(x,y),
-- ∀ u, (∀ x ∈ u, ∃ y, ϕ(x,y)) ⟹ (∃ v, ∀ z ∈ u, ∃ w ∈ v, ϕ(z,w))

def axiom_of_collection (ϕ' : bounded_formula L_ZFC' 2) : sentence L_ZFC' :=
  ∀' ((∀' (&'0 ∈' &'1 ⟹ (∃' ϕ'))) ⟹ (∃' ∀'(&'0 ∈' &'2 ⟹ ∃' ((&'0 ∈' &'2) ⊓ ϕ'))))
  -- need to do some lifting

-- axiom of union
-- ∀ u, ∃ v, ∀ x, x ∈ v ↔ ∃ y ∈ u, x ∈ y
def axiom_of_union : sentence L_ZFC' :=
∀' ∃' ∀' (&'0 ∈' &'1 ⇔ (∃' (&'0 ∈' &'3) ⊓ &'1 ∈' &'0))

lemma bSet_models_union : ⊤ ⊩[V 𝔹] axiom_of_union :=
begin
  change ⊤ ≤ _, bv_intro x, 
end

-- axiom of powerset
-- ∀ u, ∃ v, ∀ x, x ∈ v ↔ ∀ y ∈ x, y ∈ u

def axiom_of_powerset : sentence L_ZFC' :=
  ∀' ∃' ∀' (&'0 ∈' &'1 ⇔ (∀' (&'0 ∈' &'1 ⟹ &'0 ∈' &'3)))

-- axiom of infinity
-- ∃ u, ∅ ∈ u ∧ ∀ x ∈ u, ∃ y ∈ u, x ∈ y

def axiom_of_infinity : sentence L_ZFC' :=
  ∃' ((∅' ∈' &'0) ⊓ ∀'(&'0 ∈' &'1 ⟹ ∃' ((&'0 ∈' &'2) ⊓ (&'1 ∈' &'0) : bounded_formula L_ZFC' 3)))

-- axiom of regularity
-- ∀ x, ∃ y ∈ x, ∀ z' ∈ x, ¬ (z' ∈ y)

def axiom_of_regularity : sentence L_ZFC' :=
  ∀' ∃' (&'0 ∈' &'1 ⊓ ∀' (&'0 ∈' &'2 ⟹ ∼(&'0 ∈' &'1)))

/-- &1 ⊆ &0 ↔ ∀ z, (z ∈ &1 ⟹ z ∈ &0)-/
def subset' {n} (t₁ t₂ : bounded_term L_ZFC' n): bounded_formula L_ZFC' n := sorry
  -- ∀' ((&'0 ∈' t₁)) ⟹ (&'0 ∈' t₂))  -- trouble getting this to type-check

local infix ` ⊆'`:100 := subset'

-- zorns lemma
-- ∀ x, x ≠ ∅ ∧ ((∀ y, y ⊆ x ∧ ∀ w₁ w₂ ∈ y, w₁ ⊆ w₂ ∨ w₂ ⊆ w₁) → (⋃y) ∈ x)
--       → ∃ c ∈ x, ∀ z ∈ x, c ⊆ z → c = z

def zorns_lemma : sentence L_ZFC' := sorry -- need to do some casts/type ascriptions to make this type-check
  -- ∀' (∼ (&'0 ≃ ∅')
  --       ⊓ (∀' ((&'0 ⊆' &'1) ⊓ (∀' ∀' (((&'1 ∈' &'2) ⊓ (&'0 ∈' &'2)) ⟹ ((&'0 ⊆' &'2) ⊔ (&'2 ⊆' &'0)))) ⟹ (sorry/- ⋃y -/ ∈' &'2)))
  --         ⟹  (∃' (&'0 ∈' &'1) ⊓ ∀' (&'0 ∈' &'2) ⟹ &'1 ⊆' &'0 ⟹ &'1 ≃ &'0 )


-- continuum hypothesis

-- ¬ (∃ z z', ω ≺ z ≺ z' ≼ 𝒫(ω))

-- where ≺ means (¬ larger_than) and ≼ means "exists an injection into"

-- c.f. the end of `forcing.lean`

-- where "larger_than" means

-- ∃ f, is_func f ∧ ∀ v ∈ y, ∃ w ∈ x, (w,v) ∈ f

-- also need a definition of the pairing function
-- i.e. define the pairing operation and show it satisfies the axiom
-- ∀ a ∀ b ∃ c ∀ d, (d ∈ c ↔ d = a ∨ d = b)

-- need to characterize 𝒫(ω) and (ω) (powerset is an easy extensionality argument).

-- for ω, need to say that it is a subset of any other ordinal which contains all the natural numbers, which is easy
