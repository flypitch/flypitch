import .fol

open fol

/- 
  note from Mario: we can write formulae in ZFC directly, without extending the language.
  To encode "terms" of ZFC, we encode them as bounded_formula 1 (formulae with 1 free variable),
  and a formula A should be interpreted as "&0 ∈ A"
-/

namespace zfc

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

-- section test

-- /- ∀ x, ∀ y, x = y → ∀ z, z = x → z = y -/
-- def testsentence : sentence L_ZFC := ∀' ∀' (&1 ≃ &0 ⟹ ∀' (&0 ≃ &2 ⟹ &0 ≃ &1))

-- #eval print_formula testsentence --- it's alive!!

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
def pair : bounded_formula L_ZFC 3 := bd_equal &0 &1 ⊔ bd_equal &0 &2
def identity_relation : bounded_formula L_ZFC 2 := &0 ≃ &1
def singl : bounded_formula L_ZFC 2 := &0 ≃ &1
def binary_union : bounded_formula L_ZFC 3 := &0 ∈' &1 ⊔ &0 ∈' &2
def succ : bounded_formula L_ZFC 2 := bd_equal &0 &1 ⊔ &0 ∈' &1 
--∀x∃y(x ∈ y ∧ ∀z(z ∈ y → ∃w(z ∈ w ∧ w ∈ y)))




def ordered_pair : bounded_formula L_ZFC 3 := 
∀' /-w-/
  ((&0 ∈' &1) /-w ∈ z-/
  ⇔
  ( 
    (bd_equal &0 &3) ⊔ /-w = x-/
    ∀' /-v-/
      ((&0 ∈' &1) ⇔ /-v ∈ w-/
      (pair ↑' 1 # 1 ↑' 1 # 1 )))) /-v = {x,y}-/
-- &0 is an ordered pair of &2 and &1 (z = ⟨x, y⟩)

def ordered_pair' : bounded_formula L_ZFC 3 := 
∀' /-w-/
  ((&0 ∈' &3) /-w ∈ x-/
  ⇔
  ( 
    (bd_equal &0 &2) ⊔ /-w = y-/
    ∀' /-v-/
      ((&0 ∈' &1) ⇔ /-v ∈ w -/
      (pair ↑' 1 # 1 ↑' 1 # 4)))) /-v = {y,z}-/
-- &2 is an ordered pair of &1 and &0 (x = ⟨y,z⟩)

def is_ordered_pair : bounded_formula L_ZFC 1 := ∃' ∃' ordered_pair
--&0 is an ordered pair of some two elements--

def relation : bounded_formula L_ZFC 1 := ∀' ((&0 ∈' &1) ⟹ is_ordered_pair ↑' 1 # 1)
--&0 is a relation (is a set of ordered pairs)

def function : bounded_formula L_ZFC 1 := 
bd_and
  relation  
  ∀' /-x-/
    ∀' /-y-/
      ∀' /-z-/
        ∀' /-p-/
          ∀' /-q-/
            (
              ( 
                ( 
                  (&1 ∈' &5) ⊓ /-p ∈ X-/
                  (ordered_pair ↑' 1 # 3 ↑' 1 # 1 ↑' 1 # 0) /-p = ⟨x,y⟩-/
                ) ⊓
                ( 
                  (&0 ∈' &5) ⊓ /-q ∈ X-/
                  (ordered_pair ↑' 1 # 3 ↑' 1 # 2 ↑' 1 # 1 ) /-q =⟨x,z⟩-/
                )
              )    
              ⟹ 
              (bd_equal &3 &2) /-y = z-/
            )

-- X is a function iff X is a relation and the following holds:
-- ∀x ∀y ∀z ∀w ∀t, ((w ∈ X) ∧ (w = ⟨x, y⟩) ∧ (z ∈ X) ∧ (z = ⟨x, z⟩ ))) →  y = z

def fn_app : bounded_formula L_ZFC 3 := 
∃' /-p-/
  (
    (&0 ∈' &3) ⊓ /-p ∈ x-/
    (∀' /-w-/
      (
        (&0 ∈' &1) ⇔ /-w ∈ p-/
        ( 
          (bd_equal &0 &3) ⊔ /-w = y-/
          (pair ↑' 1 # 1 ↑' 1 # 4) /-w = {y,z}-/
        )
      )
    )
  )
-- ⟨y, z⟩ ∈ x 
-- &0 = &2(&1) 

def fn_domain : bounded_formula L_ZFC 2 := 
∀' /-a-/
  (
    (&0 ∈' &2) ⇔ /-a ∈ A-/
    ∃' /-b-/
      ∃' /-p-/
        (
          (ordered_pair ↑' 1 # 1 ↑' 1 # 1) ⊓ /-p = a,b-/
          (&0 ∈' &3) /-p ∈ F-/
        )
  )
-- A = dom(F)
-- &1 is the domain of &0

def fn_range : bounded_formula L_ZFC 2 := 
∀' /-b-/
  (
    (&0 ∈' &2) ⇔ 
    ∃' /-a-/
      ∃' /-q-/
        (
          (∀' /-w-/
            (
              (&0 ∈' &1) ⇔ /-w ∈ q-/
              ( 
                (bd_equal &0 &2) ⊔ /-w = a-/
                (pair ↑' 1 # 1 ↑' 1 # 4 ↑' 1 # 4) /-w = {a,b}-/
              )
            )
          ) ⊓
          (&0 ∈' &3) /-w ∈ F-/
        )
  )
-- B = Ran(F)
--&1 is the range of &0

def inverse_relation : bounded_formula L_ZFC 2 := /-X := &0, Y := &1-/
∀' /-x-/
  ((&0 ∈' &1) ⇔ /- x ∈ X -/ 
  ∃' /-u-/
    ∃' /-v-/
      ( 
        (ordered_pair' ↑' 1 # 3 ↑' 1 # 3) ⊓ /-x = ⟨u,v⟩-/
        ∃' /-y-/
          ( 
            (∀' /-w-/
              (
                (&0 ∈' &1) ⇔ /-w ∈ y-/
                (
                  (bd_equal &0 &2) ⊔/-w = v-/
                  (pair ↑' 1 # 3 ↑' 1 # 3 ↑' 1 # 3 ↑' 1 # 1)
                )
              )
            ) ⊓ /-w = {v,u}-/
            (&0 ∈' &5)))) /-y ∈ Y-/
-- &0 is the inverse relation of &1

def function_one_one : bounded_formula L_ZFC 1 := function ⊓ ∀' (inverse_relation ⟹ function ↑' 1 # 1)

def irreflexive_relation : bounded_formula L_ZFC 2 := 
relation ↑' 1 # 1 ⊓ 
∀' /-y-/
  (
    (&0 ∈' &2) /-y ∈ Y-/
    ⟹ 
    (∀' /-p-/
      (∀' /-w-/
        (&0 ∈' &1) ⇔ /-w ∈ p-/
        (bd_or
          (bd_equal &0 &2) /-w = y-/
          (∀' /-v-/
            (
              (&0 ∈' &1) ⇔ /-v ∈ w-/
              (bd_equal &0 &3) /-v = y-/
            )
          )
        )
      )
      ⟹ 
      (∼(&0 ∈' &3))
    )
  )
-- &0 is an irreflexive relation on &1

def transitive_relation : bounded_formula L_ZFC 2 := /- X := &0, Y := &1 -/
bd_and 
  (relation ↑' 1 # 1)  
  ∀' /-u-/
    ∀' /-v-/
      ∀' /-w-/
        ((
          ( 
            ( bd_and
              ( bd_and
                (&2 ∈' &4)  /-u ∈ Y -/ 
                (&1 ∈' &4)
              )  /-v ∈ Y -/
              (&0 ∈' &4)/-w ∈ Y -/
            ) ⊓
            (∃' /-p-/
              (
                (ordered_pair ↑' 1 # 1 ↑' 1 # 4 ↑' 1 # 4) ⊓ /-p = ⟨u,v⟩ -/
                (&0 ∈' &4)
              )
            )
          ) ⊓ /- p ∈ X -/
            ∃' /-q-/
              ( 
                (ordered_pair ↑' 1 # 3 ↑' 1 # 3 ↑' 1 # 3) ⊓ /-q = ⟨v,w⟩ -/
                (&0 ∈' &4))) /-q ∈ X-/
        ⟹ 
        ∃' /-r-/
          bd_and 
            (ordered_pair ↑' 1 # 2 ↑' 1 # 4 ↑' 1 # 4 ) /-r = ⟨u,w⟩ -/
            (&0 ∈' &4)) /-r ∈ X-/
--&0 is a transitive relation on &1
-- X Tr Y iff X is a relation and the following holds:
-- ∀u ∀v ∀w, (u ∈ Y ∧ v ∈ Y ∧ w ∈ Y ∧ ⟨u, v⟩ ∈ X ∧ ⟨v,w⟩ ∈ X) → ⟨u,w⟩ ∈ X 

def partial_order_zfc : bounded_formula L_ZFC 2 := irreflexive_relation ⊓ transitive_relation

def connected_relation : bounded_formula L_ZFC 2 := 
bd_and 
  (relation ↑' 1 # 1) 
  ∀' /-u-/
    ∀' /-v-/
      ((bd_and 
        (bd_and 
          (&0 ∈' &3) /-v ∈ y-/
          (&1 ∈' &3)) /-u ∈ y-/
        (∼ (bd_equal &0 &1))) /-v ≠ u-/
      ⟹ 
      ∃' /-p-/
        bd_and 
          (&0 ∈' &3) /-p ∈ X-/
          (bd_or
            (ordered_pair ↑' 1 # 3 ↑' 1 # 3) /-p = ⟨u,v⟩-/
              /-term below is "p = ⟨v,u⟩"-/
            ∀' /-w-/
              ((&0 ∈' &1) ⇔ /-w ∈ p-/
                bd_or 
                  (bd_equal &0 &2) /-w = v-/
                  (pair ↑' 1 # 1 ↑' 1 # 4 ↑' 1 # 4)))) /-w = {u,v}-/

--&0 is a connected relation on &1
-- X Con Y iff Rel(X) and ∀u ∀v (u ∈ Y ∧ v ∈ Y ∧ u ≠ v) → ⟨u,v⟩ ∈ X ∨ ⟨v, u⟩ ∈ X

def total_order : bounded_formula L_ZFC 2 := irreflexive_relation ⊓ transitive_relation ⊓ connected_relation

def well_order : bounded_formula L_ZFC 2 := /-X := &0, Y := &1-/ 
bd_and 
  (irreflexive_relation) 
  ∀' /-Z-/
    (
      ( 
        (subset ↑' 1 # 2) ⊓ /-Z ⊆ Y -/
        ∃' 
          (&0 ∈' &1)
      ) ⟹ 
    ∃' /-y-/
      ( 
        (&0 ∈' &1) ⊓ /-y ∈ Z-/
        (∀' /-v-/
          (
            (bd_and
              (&0 ∈' &2)  /-v ∈ Z -/
              ( ∼ (bd_equal &0 &1)) /-v ≠ y-/
            ) ⟹ 
            ( 
              (∃' /-p-/
                (
                  (ordered_pair ↑' 1 # 4 ↑' 1 # 4 ↑' 1 # 4) ⊓ /-p = ⟨y,v⟩-/
                  (&0 ∈' &4) /-p ∈ X -/
                )
              ) ⊓ 
              (∼ 
                (∃' /-q-/ /-first argument is q = ⟨v,y⟩-/
                  (
                    (∀' /-w-/
                      (
                        (&0 ∈' &1) ⇔ /-w ∈ q-/            
                        (
                          (bd_equal &0 &2) ⊔  /-w = v-/
                          (pair ↑' 1 # 1 ↑' 1 # 4 ↑' 1 # 4 ↑' 1 # 4)
                        )
                      )
                    ) ⊓ /-w = {v,y}-/
                    (&0 ∈' &4))))))))) /-q ∈ X-/
-- &0 well-orders &1


def membership_relation : bounded_formula L_ZFC 1 := 
relation ⊓ 
∀' 
  (
    (&0 ∈' &1) ⇔ 
    ∃' 
      ∃'
        ∀' 
        (
          (&0 ∈' &3) ⇔ 
          ( 
            (bd_equal &0 &2 ⊔ pair ↑' 1 # 3 ↑' 1 # 3) ⊓
            (&2 ∈' &1)
          )
        )
  )
-- &0 is E, the membership relation {⟨x,y⟩ | x ∈ y}

def transitive_zfc : bounded_formula L_ZFC 1 := ∀' ((&0 ∈' &1) ⟹ subset)
--&0 is transitive

def fn_zfc_equiv : bounded_formula L_ZFC 3 := 

  (
    (function_one_one ↑' 1 # 1 ↑' 1 # 1) ⊓
    (fn_domain ↑' 1 # 1)) ⊓
  (fn_range ↑' 1 # 2)

def zfc_equiv : bounded_formula L_ZFC 2 := ∃' fn_zfc_equiv
--&0 ≃ &1, i.e. they are equinumerous

def is_powerset : bounded_formula L_ZFC 2 := ∀' ((&0 ∈' &2) ⇔ subset ↑' 1 # 2)
--&1 is P(&0)

def is_suc_of : bounded_formula L_ZFC 2 := 
∀' 
  ((&0 ∈' &2) ⇔ 
  (
    (&0 ∈' &1) ⊔
    (bd_equal &0 &1)))
-- &1 = succ(&0)

def is_ordinal : bounded_formula L_ZFC 1 := 
  (∀' ((membership_relation ↑' 1 # 1) ⟹ well_order)) ⊓
  transitive_zfc

def is_suc_ordinal : bounded_formula L_ZFC 1 := is_ordinal ⊓ ∃' is_suc_of
--&0 is a successor ordinal

def ordinal_lt : bounded_formula L_ZFC 2 := (is_ordinal ↑' 1 # 1) ⊓ (is_ordinal ↑' 1 # 0) ⊓ (&0 ∈' &1)
-- &0 < &1

def ordinal_le : bounded_formula L_ZFC 2 := ordinal_lt ⊔ (bd_equal &0 &1)
-- &0 ≤ &1

def is_first_ordinal : bounded_formula L_ZFC 1 := 
∀' 
  (
    (&0 ∈' &1) ⇔ 
    (
      ((is_emptyset ⊔ is_suc_ordinal)↑' 1 # 1) ⊓
      ∀' 
        (
          (&0 ∈' &1) 
          ⟹ 
          ((is_emptyset ⊔ is_suc_ordinal) ↑' 1 # 1 ↑' 1 # 1)
        )
    )
  )
--&0 = ω

def is_uncountable_ordinal : bounded_formula L_ZFC 1 := 
∀' 
  ((is_first_ordinal ↑' 1 # 1) ⟹ 
  ∀' 
    (subset ↑' 1 # 2 ⟹ 
    (∼(zfc_equiv ↑' 1 # 1))))
--&0 ≥ ω₁

def is_first_uncountable_ordinal : bounded_formula L_ZFC 1 := is_uncountable_ordinal ⊓ (∀' ((is_uncountable_ordinal ↑' 1 # 1) ⟹ ordinal_le))
--&0 = ω₁



def continuum_hypothesis : sentence L_ZFC := 
∀' 
  ∀' 
    (( 
      (∃' 
          ((is_first_ordinal ↑' 1 # 1 ↑' 1 # 1) ⊓
          (is_powerset↑' 1 # 2))) ⊓ 
      (is_first_uncountable_ordinal ↑' 1 #0)) ⟹  
    zfc_equiv)



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
-- for every E : A → B, there exists a function C on A such that for every a ∈ A, C a ∈ E a (if E a is nonempty).
  ∀' /-E-/  
    (∀' /-A-/
      (fn_domain ⟹ 
        (∃' /-C-/                 
          (∀' /-a-/ 
            ((&0 ∈' &2) ⟹         
              (∀' /-b-/
                ( (fn_app ↑' 1 # 2 ↑' 1 # 2) ⟹ /-&0 = &4(&1) ;  b = E(a)-/
                  ((∀' /-c-/
                    ( 
                      (fn_app ↑' 1 # 1 ↑' 1 # 4 ↑' 1 # 4) ⊓ /-&0 = &3(&2) ; c = C(a)-/
                      (∃' (&0 ∈' &2)) /- b is nonempty -/
                    ) ⟹ (&0 ∈' &1))))))))))  
-- ∀E, function(E) ⇒  ∀ A, A = dom(E) ⇒ ∃ C, ∀ a, (a ∈ A ⇒ (∀ b, (fn_app E a b) ⇒ ∀ c, (fn_app C a c ∧ (∃'z, z ∈ b)) ⇒ c ∈ b))

-- the following axioms follow from the other axioms
def axiom_of_emptyset : sentence L_ZFC := small ⊥
-- todo: c can have free variables
def axiom_of_separation (c : Class) : sentence L_ZFC := ∀' (small $ &0 ∈' &1 ⊓ c.cast1)
-- the class consisting of the unordered pair {x, y}
def axiom_of_pairing : sentence L_ZFC := ∀' ∀' small pair
--the class consisting of the ordered pair ⟨x, y⟩
def axiom_of_ordered_pairing : sentence L_ZFC := ∀' ∀' small ordered_pair
--the class consisting of all ordered pairs
def axiom_of_product : sentence L_ZFC := small is_ordered_pair

def ZF : Theory L_ZFC := {axiom_of_extensionality, axiom_of_union, axiom_of_powerset, axiom_of_infinity} ∪ (λ(c : bounded_formula L_ZFC 2), axiom_of_replacement c) '' set.univ

def ZFC : Theory L_ZFC := ZF ∪ {axiom_of_choice}

end zfc
