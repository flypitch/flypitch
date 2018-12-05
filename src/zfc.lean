import .fol

open fol

/- 
  note from Mario: we can write formulae in ZFC directly, without extending the language.
  To encode "terms" of ZFC, we encode them as bounded_formula 1 (formulae with 1 free variable),
  and a formula A should be interpreted as "&0 ∈ A"
-/

section zfc

inductive ZFC_rel : ℕ → Type
| ϵ : ZFC_rel 2

def L_ZFC : Language := 
⟨λ_, empty, ZFC_rel⟩

def ZFC_el : L_ZFC.relations 2 := ZFC_rel.ϵ

local infix ` ∈' `:100 := bounded_formula_of_relation ZFC_el


inductive ZFC'_f0 : Type
| emptyset

inductive ZFC'_f1 : Type
| union
| pow

inductive ZFC'_f2 : Type
| pair

inductive ZFC'_rel : Type
| ϵ
| subset 

def L_ZFC' : Language :=
begin
split,
{intro arityf,
exact if arityf = 0
      then ZFC'_f0
      else (if arityf = 1
           then ZFC'_f1
           else (if arityf = 2
                then ZFC'_f2
                else empty))   },
{
{intro arityr,
exact if arityr = 2 then ZFC'_rel else empty},
}
end

-- is there a way to do this with the equation compiler instead?

lemma duh : L_ZFC'.relations 2 = ZFC'_rel :=
by refl

@[reducible]def rel_is_rel : ZFC'_rel → L_ZFC'.relations 2 :=
begin
intro,
rw[duh],
assumption
end

def Class : Type := bounded_formula L_ZFC 1
def small {n} (c : bounded_formula L_ZFC (n+1)) : bounded_formula L_ZFC n := 
∃' ∀' (&0 ∈' &1 ⇔ (c ↑' 1 # 1))
def subclass (c₁ c₂ : Class) : sentence L_ZFC := ∀' (c₁ ⟹ c₂)
def functional {n} (c : bounded_formula L_ZFC (n+2)) : bounded_formula L_ZFC n := 
-- ∀x ∃y ∀z, c z x ↔ z = y
∀' ∃' ∀' (c ↑' 1 # 1 ⇔ &0 ≃ &1)
def subset : bounded_formula L_ZFC 2 := ∀' (&0 ∈' &1 ⟹ &0 ∈' &2)
def pair : bounded_formula L_ZFC 3 := bd_equal &0 &1 ⊔ bd_equal &0 &2
def singl : bounded_formula L_ZFC 2 := &0 ≃ &1
def binary_union : bounded_formula L_ZFC 3 := &0 ∈' &1 ⊔ &0 ∈' &2
def succ : bounded_formula L_ZFC 2 := bd_equal &0 &1 ⊔ &0 ∈' &1
--∀x∃y(x ∈ y ∧ ∀z(z ∈ y → ∃w(z ∈ w ∧ w ∈ y)))

def function : bounded_formula L_ZFC 1 := sorry
-- to define what functions are, we need to have a notion of what it means for a set to be made up of only ordered pairs, but this seems... ugly

def axiom_of_extensionality : sentence L_ZFC := ∀' ∀' (∀' (&0 ∈' &1 ⇔ &0 ∈' &2) ⟹ &0 ≃ &1)
def axiom_of_union : sentence L_ZFC := ∀' (small ∃' (&1 ∈' &0 ⊓ &0 ∈' &2))
-- todo: c can have free variables. Note that c y x is interpreted as y is the image of x
def axiom_of_replacement (c : bounded_formula L_ZFC 2) : sentence L_ZFC := 
-- ∀α small (λy, ∃x, x ∈ α ∧ c y x)
functional c ⟹ ∀' (small ∃' (&0 ∈' &2 ⊓ c.cast1))
def axiom_of_powerset : sentence L_ZFC := 
-- the class of all subsets of x is small
∀' small subset
def axiom_of_infinity : sentence L_ZFC := 
--∀x∃y(x ∈ y ∧ ∀z(z ∈ y → ∃w(z ∈ w ∧ w ∈ y)))
∀' ∃' (&1 ∈' &0 ⊓ ∀'(&0 ∈' &1 ⟹ ∃' (bd_and (&1 ∈' &0) (&0 ∈' &2))))
def axiom_of_choice : sentence L_ZFC :=
-- for every E : A → B, there exists a function C on A such that for every a ∈ A, C a ∈ E a.
  ∀' /-E : A → B-/ ∃' /- C -/ ∀' /- a -/ /- if a is in the domain of E and E a is nonempty, then C a ∈ E a -/ sorry
-- the following axioms follow from the other axioms
def axiom_of_emptyset : sentence L_ZFC := small ⊥
-- todo: c can have free variables
def axiom_of_separation (c : Class) : sentence L_ZFC := ∀' (small $ &0 ∈' &1 ⊓ c.cast1)
-- the class consisting of the unordered pair {x, y}
def axiom_of_pairing : sentence L_ZFC := ∀' ∀' small pair


-- inductive ZFC' : (@sentence L_ZFC') → Prop -- should this be Type-valued instead?
-- := sorry

end zfc

