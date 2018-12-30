import .fol tactic.tidy tactic.ring

open fol

local notation h :: t  := dvector.cons h t
local notation `[]` := dvector.nil
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

namespace abel
section

/- The language of abelian groups -/
inductive abel_functions : ℕ → Type
| zero : abel_functions 0
| plus : abel_functions 2

def L_abel : Language := ⟨abel_functions, λn, empty⟩

def L_abel_plus {n} (t₁ t₂ : bounded_term L_abel n) : bounded_term L_abel n := 
@bounded_term_of_function L_abel 2 n abel_functions.plus t₁ t₂

def zero {n} : bounded_term L_abel n := bd_const abel_functions.zero

local infix ` +' `:100 := L_abel_plus

def a_assoc : sentence L_abel := ∀' ∀' ∀' (((&2 +' &1) +' &0) ≃ (&2 +' (&1 +' &0)))

def a_zero_right : sentence L_abel := ∀' (&0 +' zero ≃ &0)

def a_zero_left : sentence L_abel := ∀'(zero +' &0 ≃ &0)

def a_inv : sentence L_abel := ∀' ∃' (&1 +' &0 ≃ zero ⊓ &0 +' &1 ≃ zero)

def a_comm : sentence L_abel := ∀' ∀' (&1 +' &0 ≃ &0 +' &1)

/- axioms of abelian groups -/
def Th_ab : Theory L_abel := {a_assoc, a_zero_right, a_zero_left, a_inv, a_comm}

def L_abel_structure_of_int : Structure L_abel :=
begin
  refine ⟨ℤ,_,_⟩,
  {intros n f, induction f,
    exact λ v, 0,
    exact λ v, (v.nth 0 (by repeat{constructor})) + (v.nth 1 (by repeat{constructor}))},
  {intros, cases a}
end

local notation `ℤ'` := L_abel_structure_of_int

@[simp]lemma ℤ'_ℤ : ↥(ℤ') = ℤ := by refl

@[reducible]instance has_zero_ℤ' : has_zero ℤ' := ⟨(0 : ℤ)⟩

@[reducible]instance has_add_ℤ' : has_add ℤ' := ⟨λx y, (x + y : ℤ)⟩

@[simp]lemma zero_is_zero : @realize_bounded_term L_abel ℤ' _ [] _ zero [] = (0 : ℤ) := by refl

@[simp]lemma plus_is_plus_l : ∀ x y : ℤ', realize_bounded_term ([x,y]) (&0 +' &1) [] = x + y := by {intros, refl}

@[simp]lemma plus_is_plus_r : ∀ x y : ℤ', realize_bounded_term ([x,y]) (&1 +' &0) [] = y + x := by {intros, refl}

def presburger_arithmetic : Theory L_abel := Th ℤ'

theorem ℤ'_is_abelian_group : Th_ab ⊆ presburger_arithmetic :=
begin
  intros a H, repeat{cases H},
  {tidy},
  {intros x H, dsimp at H, unfold realize_bounded_formula, have : ∃ y : ℤ, x + y = 0,
  by exact ⟨-x, by tidy⟩, rcases this with ⟨y, hy⟩, have := H y, apply this, simp[hy], refl},
  {tidy, conv {to_lhs, change (0 : ℤ) + x, rw[zero_add]}, refl},
  {tidy, conv {to_lhs, change x + 0, rw[add_zero]}, refl},
  {tidy, conv {to_lhs, change x + x_1 + x_2}, finish}
end

end
end abel
