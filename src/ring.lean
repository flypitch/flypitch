/-
  The first-order theory of rings (experimental)
-/

import .fol .abel .language_extension

open fol abel

universe u

namespace L_ring

/--
  The language of rings is (0,1,+,×), extending the language of abelian groups
-/
inductive L_ring_functions : ℕ → Type u
| of_abel : ∀ n : ℕ, L_abel.functions n → L_ring_functions n
| one     : L_ring_functions 0
| times   : L_ring_functions 2

def L_ring : Language.{u} := ⟨L_ring_functions, λ _, pempty⟩

def L_ring_plus {n} (t₁ t₂ : bounded_term L_ring n) : bounded_term L_ring n :=
@bounded_term_of_function L_ring 2 n (L_ring_functions.of_abel _ (abel_functions.plus)) t₁ t₂

-- @bounded_term_of_function L_ring 2 n (L_ring_functions.of_abel (L_abel.plus)) t₁ t₂

def L_ring_times {n} (t₁ t₂ : bounded_term L_ring n) : bounded_term L_ring n :=
@bounded_term_of_function L_ring 2 n L_ring_functions.times t₁ t₂


local infix ` +' `:100 := L_ring_plus
local infix ` ×' `:100 := L_ring_times

def to_L_ring : L_abel →ᴸ L_ring :=
{ on_function := λ n, L_ring_functions.of_abel n,
  on_relation := λ _, pempty.elim }

def zero {n} : bounded_term L_ring n := Lhom.on_bounded_term (to_L_ring) (abel.zero)

def one {n} : bounded_term L_ring n := bd_const (L_ring_functions.one)

/-
  Axioms of a ring:
   - it is an abelian group, and
   - multiplication is associative and has an identity, and
   - multiplication is left and right distributive
-/

def mul_assoc : sentence L_ring := ∀' ∀' ∀' (((&2 ×' &1) ×' &0) ≃ (&2 ×' (&1 ×' &0)))
def mul_id_left : sentence L_ring := ∀'(one ×' &0 ≃ &0)
def mul_id_right : sentence L_ring := ∀' (&0 ×' one ≃ &0)
def mul_dist_left : sentence L_ring := ∀' ∀' ∀' ((&2 ×' (&1 +' &0)) ≃ (&2 ×' &1) +' (&2 ×' &0))
def mul_dist_right : sentence L_ring := ∀' ∀' ∀' (((&1 +' &0) ×' &2) ≃ (&1 ×' &2) +' (&0 ×' &2))

def T_ring : Theory L_ring :=
(Lhom.on_sentence (to_L_ring) '' T_ab) ∪
           {mul_assoc, mul_id_left, mul_id_right, mul_dist_left, mul_dist_right}

/-
  A commutative ring satisfies the additional axiom that multiplication is commutative
-/


def mul_comm : sentence L_ring := ∀' ∀' (&1 ×' &0 ≃ &0 ×' &1) 

def T_comm_ring : Theory L_ring := T_ring ∪ {mul_comm}

end L_ring
