import .fol set_theory.zfc

open fol

inductive ZFC_rel : ℕ → Type
| ϵ : ZFC_rel 2

def L_ZFC : Language := 
⟨λ_, empty, ZFC_rel⟩

def ZFC_el : L_ZFC.relations 2 := ZFC_rel.ϵ

local infix ` ∈' `:100 := bounded_formula_of_relation ZFC_el

---ugly but working (str_formula says it's not well-founded recursion, but it evaluates anyways)
def str_preterm : ∀ n m : ℕ, ℕ → bounded_preterm L_ZFC n m → string
  | n m z &k := "x" ++ to_string(z - k)
  | _ _ _ _ := "h"
def str_term: ∀ n : ℕ, ℕ → bounded_term L_ZFC n → string
  | n m &k := "x" ++ to_string(m - k.val)
  | _ _ _ := "n"
def str_preformula : ∀ n m : ℕ, ℕ → bounded_preformula L_ZFC n m → string
  | _ _ _ (bd_falsum ) := "⊥"
  | n m z (bd_equal a b) := str_preterm n m z a ++ " = " ++ str_preterm n m z b
  | n m z (a ⟹ b) := str_preformula n m z a ++ " ⟹ " ++ str_preformula n m z b
  | n m z (bd_rel _) := "∈"
  | n m z (bd_apprel a b) := str_preformula n (m+1) z a ++ "(" ++ str_term n z b ++ ")"
  | n m z (∀' t) := "(∀x" ++ to_string(z+1) ++ "," ++ str_preformula (n+1) m (z+1) t ++ ")"
def str_formula : ∀ {n : ℕ}, bounded_formula L_ZFC n → ℕ → string
  | n ((f₁ ⟹ (f₂ ⟹ bd_falsum)) ⟹ bd_falsum) m:= "(" ++ str_formula f₁ m ++ "∧" ++ str_formula f₂ m ++ ")"
  | n ((f₁ ⟹ bd_falsum) ⟹ f₂) m := "(" ++ str_formula f₁ m ++ " ∨ " ++ str_formula f₂ m ++ ")"
  | n (bd_equal s1 s2) m := "(" ++ str_term n m s1 ++ " = " ++ str_term n m s2 ++ ")"
  | n (∀' f) m := "(∀x"++ to_string(m + 1) ++ "," ++ (str_formula f (m+1) ) ++ ")"
  | _ bd_falsum _ := "⊥"
  | n (f ⟹ bd_falsum) m := "~" ++ str_formula f m
  | n (bd_apprel (f₁) f₂) m := str_preformula n 1 m f₁ ++ "(" ++ str_term n m f₂ ++ ")"
  | n (bd_imp a b) m := "(" ++ str_formula a m ++ " ⟹ " ++ str_formula b m ++ ")"

def print_formula : ∀ {n : ℕ}, bounded_formula L_ZFC n → string := λ n f, str_formula f n

notation `lift_cast` := by {repeat{apply nat.succ_le_succ}, apply nat.zero_le}

-- section test

-- /- ∀ x, ∀ y, x = y → ∀ z, z = x → z = y -/
-- def testsentence : sentence L_ZFC := ∀' ∀' (&1 ≃ &0 ⟹ ∀' (&0 ≃ &2 ⟹ &0 ≃ &1))
-- end test

----------------------------------------------------------------------------
def Class : Type := bounded_formula L_ZFC 1
def small {n} (c : bounded_formula L_ZFC (n+1)) : bounded_formula L_ZFC n := 
∃' ∀' (&0 ∈' &1 ⇔ (c ↑' 1 # 1))
def subclass (c₁ c₂ : Class) : sentence L_ZFC := ∀' (c₁ ⟹ c₂)
def functional {n} (c : bounded_formula L_ZFC (n+2)) : bounded_formula L_ZFC n := 
-- ∀x ∃y ∀z, c z x ↔ z = y
∀' ∃' ∀' (c ↑' 1 # 1 ⇔ &0 ≃ &1)
def subset : bounded_formula L_ZFC 2 := ∀' (&0 ∈' &1 ⟹ &0 ∈' &2)
def is_emptyset : bounded_formula L_ZFC 1 := ∼ ∃' (&0 ∈' &1) 
def pair : bounded_formula L_ZFC 3 := (&0 ≃ &1 : bounded_formula L_ZFC 3) ⊔ (&0 ≃ &2 : bounded_formula L_ZFC 3)
def singl : bounded_formula L_ZFC 2 := &0 ≃ &1
def binary_union : bounded_formula L_ZFC 3 := &0 ∈' &1 ⊔ &0 ∈' &2
def succ : bounded_formula L_ZFC 2 := (&0 ≃ &1 : bounded_formula L_ZFC 2) ⊔ &0 ∈' &1 

def ordered_pair : bounded_formula L_ZFC 3 := ∀'(&0 ∈' &1 ⇔ (&0 ≃ &3 : bounded_formula L_ZFC 4) ⊔ ∀'(&0 ∈' &1 ⇔ pair ↑' 1 # 1 ↑' 1 # 1))
-- &0 is an ordered pair of &2 and &1 (z = ⟨x, y⟩)

def ordered_pair' : bounded_formula L_ZFC 3 := ∀'(&0 ∈' &3 ⇔ (&0 ≃ &2 : bounded_formula L_ZFC 4) ⊔ ∀'(&0 ∈' &1 ⇔ (pair ↑' 1 # 1).cast(lift_cast)))
-- &2 is an ordered pair of &1 and &0 (x = ⟨y,z⟩)

def is_ordered_pair : bounded_formula L_ZFC 1 := ∃' ∃' ordered_pair
--&0 is an ordered pair of some two elements--

def relation : bounded_formula L_ZFC 1 := ∀' ((&0 ∈' &1) ⟹ is_ordered_pair ↑' 1 # 1)
--&0 is a relation (is a set of ordered pairs)

def function : bounded_formula L_ZFC 1 := relation ⊓ ∀'∀'∀'∀'∀'(&1 ∈' &5 ⊓ ordered_pair ↑' 1 # 3 ↑' 1 # 1 ↑' 1 # 0 ⊓ ((&0 ∈' &5 : bounded_formula L_ZFC 6) ⊓ (ordered_pair ↑' 1 # 2 ↑' 1 # 1).cast(lift_cast)) ⟹ (&3 ≃ &2 : bounded_formula L_ZFC 6))
-- X is a function iff X is a relation and the following holds:
-- ∀x ∀y ∀z ∀w ∀t, ((w ∈ X) ∧ (w = ⟨x, y⟩) ∧ (z ∈ X) ∧ (z = ⟨x, z⟩ ))) →  y = z

def fn_app : bounded_formula L_ZFC 3 := ∃'(&0 ∈' &3 ⊓ ∀'(&0 ∈' &1 ⇔ ((&0 ≃ &3): bounded_formula L_ZFC 5) ⊔ (pair ↑' 1 # 1).cast(lift_cast)))
-- ⟨&1, &0⟩ ∈ &2 
-- &0 = &2(&1) 

def fn_domain : bounded_formula L_ZFC 2 := ∀'(&0 ∈' &2 ⇔ ∃'∃'(ordered_pair ↑' 1 # 1 ↑' 1 # 1 ⊓ &0 ∈' &3))
-- &1 is the domain of &0

def fn_range : bounded_formula L_ZFC 2 := ∀'(&0 ∈' &2 ⇔ ∃'∃'(∀'(&0 ∈' &1 ⇔ (&0 ≃ &2 : bounded_formula L_ZFC 6) ⊔ (pair ↑' 1 # 1).cast(lift_cast)) ⊓ &0 ∈' &3))
--&1 is the range of &0

def inverse_relation : bounded_formula L_ZFC 2 := ∀'(&0 ∈' &1 ⇔ ∃'∃'(∃'(∀'(&0 ∈' &1 ⇔ (&0 ≃ &2 : bounded_formula L_ZFC 7) ⊔ (pair ↑' 1 # 1).cast(lift_cast)) ⊓ &0 ∈' &5 : bounded_formula L_ZFC 6)) ⊓ (ordered_pair'.cast(lift_cast)))
-- &0 is the inverse relation of &1

def function_one_one : bounded_formula L_ZFC 1 := function ⊓ ∀' (inverse_relation ⟹ function.cast(lift_cast))

def irreflexive_relation : bounded_formula L_ZFC 2 :=  (∀'(&0 ∈' &2 ⟹ (∀'(∀'(&0 ∈' &1) ⇔ ((&0 ≃ &2 : bounded_formula L_ZFC 4) ⊔ ∀'(&0 ∈' &1 ⇔ (&0 ≃ &3 : bounded_formula L_ZFC 5))) ⟹ ∼(&0 ∈' &3))))) ⊓ relation.cast(lift_cast)
-- &0 is an irreflexive relation on &1

def transitive_relation : bounded_formula L_ZFC 2 := ((∀'∀'∀'((((&2 ∈' &4 : bounded_formula L_ZFC 5) ⊓ (&1 ∈' &4)) ⊓ (&0 ∈' &4)) ⊓ ∃'((ordered_pair ↑' 1 # 1).cast(lift_cast) ⊓ (&0 ∈' &4 : bounded_formula L_ZFC 6)) ⊓ ∃'(ordered_pair.cast(lift_cast) ⊓ &0 ∈' &4 : bounded_formula L_ZFC 6) ⟹ ∃'((ordered_pair ↑' 1 # 2).cast(lift_cast) ⊓ &0 ∈' &4 : bounded_formula L_ZFC 6)))) ⊓ relation.cast(lift_cast) 
--&0 is a transitive relation on &1
-- X Tr Y iff X is a relation and the following holds:
-- ∀u ∀v ∀w, (u ∈ Y ∧ v ∈ Y ∧ w ∈ Y ∧ ⟨u, v⟩ ∈ X ∧ ⟨v,w⟩ ∈ X) → ⟨u,w⟩ ∈ X 

def partial_order_zfc : bounded_formula L_ZFC 2 := irreflexive_relation ⊓ transitive_relation

def connected_relation : bounded_formula L_ZFC 2 := relation ↑' 1 # 1 ⊓ ∀'∀'((bd_and (bd_and (&0 ∈' &3) (&1 ∈' &3)) ∼(bd_equal &0 &1)) ⟹ ∃'((&0 ∈' &3 : bounded_formula L_ZFC 5) ⊓ ((ordered_pair ↑' 1 # 3 ↑' 1 # 3) ⊔ ∀'(&0 ∈' &1 ⇔ (&0 ≃ &2 : bounded_formula L_ZFC 6) ⊔ (pair ↑' 1 # 1).cast(lift_cast)))))
--&0 is a connected relation on &1
-- X Con Y iff Rel(X) and ∀u ∀v (u ∈ Y ∧ v ∈ Y ∧ u ≠ v) → ⟨u,v⟩ ∈ X ∨ ⟨v, u⟩ ∈ X

def total_order : bounded_formula L_ZFC 2 := irreflexive_relation ⊓ transitive_relation ⊓ connected_relation

def well_order : bounded_formula L_ZFC 2 := irreflexive_relation ⊓ ∀'(subset ↑' 1 # 2 ⊓ ∃'(&0 ∈' &1) ⟹ ∃'(&0 ∈' &1 ⊓ ∀'(((&0 ∈' &2) ⊓  ∼(&0 ≃ &1 : bounded_formula L_ZFC 5)) ⟹ ∃'(ordered_pair.cast(lift_cast) ⊓ (&0 ∈' &4 : bounded_formula L_ZFC 6)) ⊓ ∼∃'(∀'(&0 ∈' &1 ⇔ (( &0 ≃ &2 : bounded_formula L_ZFC 7) ⊔ (pair ↑' 1 # 1).cast(lift_cast) )) ⊓ &0 ∈' &4))))
-- &0 well-orders &1

def membership_relation : bounded_formula L_ZFC 1 := relation ⊓ ∀'(&0 ∈' &1 ⇔ ∃'∃'∀'(&0 ∈' &3 ⇔ ((bd_equal &0  &2) ⊔ pair ↑' 1 # 3 ↑' 1 # 3) ⊓ &2 ∈' &1))
-- &0 is E, the membership relation {⟨x,y⟩ | x ∈ y}

def transitive_zfc : bounded_formula L_ZFC 1 := ∀' ((&0 ∈' &1) ⟹ subset)
--&0 is transitive

def fn_zfc_equiv : bounded_formula L_ZFC 3 := ((function_one_one.cast(lift_cast)) ⊓ (fn_domain ↑' 1 # 1)) ⊓ (fn_range ↑' 1 # 2)

def zfc_equiv : bounded_formula L_ZFC 2 := ∃' fn_zfc_equiv
--&0 ≃ &1, i.e. they are equinumerous

def is_powerset : bounded_formula L_ZFC 2 := ∀' ((&0 ∈' &2) ⇔ subset ↑' 1 # 2)
--&1 is P(&0)

def is_suc_of : bounded_formula L_ZFC 2 := ∀' ((&0 ∈' &2) ⇔ ((&0 ∈' &1) ⊔ ( &0 ≃ &1 : bounded_formula L_ZFC 3)))
-- &1 = succ(&0)

def is_ordinal : bounded_formula L_ZFC 1 := (∀' ((membership_relation.cast(lift_cast)) ⟹ well_order)) ⊓ transitive_zfc

def is_suc_ordinal : bounded_formula L_ZFC 1 := is_ordinal ⊓ ∃' is_suc_of
--&0 is a successor ordinal

def ordinal_lt : bounded_formula L_ZFC 2 := (is_ordinal.cast(lift_cast)) ⊓ (is_ordinal ↑' 1 # 0) ⊓ (&0 ∈' &1)
-- &0 < &1

def ordinal_le : bounded_formula L_ZFC 2 := ordinal_lt ⊔ (bd_equal &0 &1)
-- &0 ≤ &1

def is_first_infinite_ordinal : bounded_formula L_ZFC 1 := ∀' ((&0 ∈' &1) ⇔ (((is_emptyset ⊔ is_suc_ordinal)↑' 1 # 1) ⊓ ∀'((&0 ∈' &1) ⟹ ((is_emptyset ⊔ is_suc_ordinal).cast(lift_cast)))))
--&0 = ω

def is_uncountable_ordinal : bounded_formula L_ZFC 1 := ∀' ((is_first_infinite_ordinal.cast(lift_cast)) ⟹ ∀' (subset.cast(lift_cast) ⟹(∼(zfc_equiv ↑' 1 # 1))))
--&0 ≥ ω₁

def is_first_uncountable_ordinal : bounded_formula L_ZFC 1 := is_uncountable_ordinal ⊓ (∀' ((is_uncountable_ordinal ↑' 1 # 1) ⟹ ordinal_le))
--&0 = ω₁

/- Statement of CH -/
def continuum_hypothesis : sentence L_ZFC := ∀' ∀'  ((∃'((is_first_infinite_ordinal ↑' 1 # 1 ↑' 1 # 1) ⊓ (is_powerset ↑' 1 # 2)) ⊓ (is_first_uncountable_ordinal ↑' 1 #0)) ⟹ zfc_equiv)

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

def axiom_of_choice : sentence L_ZFC := ∀'∀'(fn_domain ⟹ ∃'∀'(&0 ∈' &2 ⟹∀'(fn_app ↑' 1 # 2 ↑' 1 # 2 ⟹ (∀'(fn_app ↑' 1 # 1 ↑' 1 # 4 ↑' 1 # 4 ⊓ ∃'(&0 ∈' &2)) ⟹ &0 ∈' &1))))

def axiom_of_emptyset : sentence L_ZFC := small ⊥
-- todo: c can have free variables
def axiom_of_separation (c : Class) : sentence L_ZFC := ∀' (small $ &0 ∈' &1 ⊓ c.cast1)
-- the class consisting of the unordered pair {x, y}
def axiom_of_pairing : sentence L_ZFC := ∀' ∀' small pair
--the class consisting of the ordered pair ⟨x, y⟩
def axiom_of_ordered_pairing : sentence L_ZFC := ∀' ∀' small ordered_pair

def ZF : Theory L_ZFC := {axiom_of_extensionality, axiom_of_union, axiom_of_powerset, axiom_of_infinity} ∪ (λ(c : bounded_formula L_ZFC 2), axiom_of_replacement c) '' set.univ

def ZFC : Theory L_ZFC := ZF ∪ {axiom_of_choice}
namespace pSet
def L_ZFC_structure_of_set : Structure L_ZFC := 
begin
  refine ⟨Set, _, _ ⟩
  admit
end

end zfc
