/- 9/20/18 
    Preliminary definitions and some functions for working with languages and first-order logic.
    Much of the structure and methods are taken from Russell O'Connor's proof of Goedel's incompleteness theorem, at http://r6.ca/Goedel/goedel1.html
    Andrew Tindall-/

structure Language := 
    language :: (relations : Π n : nat, Type) (functions : Π  n : nat, Type) (consts : Type)
variable L : Language

def term_param := unit ⊕ nat
def atm :term_param := sum.inl ()
def vec : nat → term_param := λ n, sum.inr n

inductive term : Π n, Type 
    | var : ℕ → term atm
    | const: L.consts → term atm
    | apply : ∀ (n : nat) (f : L.functions n), term (vec n) → term atm
    | nil : term (vec 0)
    | conj : ∀ n, term atm → term (vec n) → term (vec (n + 1))
    
open term

local notation `⟦` l:(foldr `, ` (h t, ((prod.fst t) + 1, conj t.fst h (prod.snd t))) (0, nil L) `⟧`) := prod.snd l


def term_sizeof :Π n, term L n → ℕ 
    | atm (var L n) := 0
    | atm (const c) := 0
    | atm (apply n f ts) :=  n + 2 + term_sizeof (vec n) ts
    | (sum.inr 0) (nil L) := 0
    | (sum.inr (n+1)) (conj m t ts) := 1 + term_sizeof atm t + term_sizeof (vec m) ts

instance term_has_sizeof { n: term_param}  : has_sizeof (term L n) := ⟨ term_sizeof L n ⟩ 


inductive formula : Type 
    | equal : term L atm → term L atm → formula
    | atomic : ∀ (n : nat) (r : L.relations n), term L (vec n) → formula 
    | imp : formula → formula → formula
    | not : formula → formula
    | all : ℕ → formula → formula
open formula

def andf := λ (f : formula L) g, not (imp f (not g))

reserve infix `⟾`:10
infix ⟾ := imp

reserve infix `⇔`:15
local infix ⇔ := λ (f : formula L) g, andf L (f ⟾ g) (g ⟾ f)

reserve infix `≍`:20
infix ≍ := equal

def free_vars_term : Π n, (term L n) → list ℕ 
    | atm (var L n) := [n]
    | atm (const c) := []
    | atm (apply n f ts) := free_vars_term (vec n) ts
    | (sum.inr 0) _ := []
    | (sum.inr (n+1)) (conj m t ts) := list.union (free_vars_term atm t) (free_vars_term (vec n) ts)

def free_vars_formula : formula L → list ℕ 
    | (equal t1 t2) := list.union (free_vars_term L atm t1) (free_vars_term L atm t2)
    | (atomic n r ts) := free_vars_term L (vec n) ts
    | (imp f1 f2) := list.union (free_vars_formula f1) (free_vars_formula f2)
    | (not f) := free_vars_formula f
    | (all n f) := list.filter (≠ n) (free_vars_formula f)


lemma lt_add : ∀ (n m k : ℕ), n < m → n < k + m:= begin {intros n m k n_lt_m, induction k, rw zero_add,exact n_lt_m, rw nat.succ_add, apply nat.lt_succ_of_lt,exact k_ih} end
lemma add_lt : ∀ (n m k : ℕ), n < m → n < m + k := begin {intros n m k n_lt_m, induction k, rw add_zero,exact n_lt_m, rw nat.add_comm, rw nat.succ_add, apply nat.lt_succ_of_lt, rw nat.add_comm, exact k_ih} end

def substitute_term : Π (n : term_param), term L n → list (nat × term L atm) → term L n
    | atm (var L n) [] := var L n
    | atm (var L n) ((m, t) :: pairs) := if n = m then t else substitute_term atm (var L n) pairs
    | atm (const c) _ := const c
    | atm (apply n f ts) pairs := 
            have term_sizeof L (vec n) ts < term_sizeof L atm (apply n f ts), from 
                begin simp[term_sizeof], 
                    apply lt_add,
                    exact nat.lt_add_of_pos_right (nat.zero_lt_succ 1) 
                end,
        apply n f (substitute_term (sum.inr n) ts pairs)
    | (sum.inr 0) a b := nil L
    | (sum.inr n) (conj m t ts) pairs := 
            have term_sizeof L atm t < term_sizeof L (sum.inr (m + 1)) (conj m t ts), from 
                begin 
                    simp [term_sizeof, nat.add_assoc], simp [nat.one_add], 
                    apply nat.lt_succ_of_le, 
                    apply nat.le_add_right  
                end,
            have term_sizeof L (vec m) ts < term_sizeof L (sum.inr (m + 1)) (conj m t ts), from 
                begin 
                    simp [term_sizeof, nat.one_add], 
                    apply nat.lt_add_of_pos_left, 
                    apply nat.zero_lt_succ 
                end,
        conj m (substitute_term atm t pairs) (substitute_term (vec m) ts pairs)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf psigma.sizeof⟩]}

def var_in_term : ∀ n, ℕ → term L n → Prop
    | atm x (var L y) := x = y
    | atm _ (const c) := false
    | atm x (apply n f ts) := var_in_term (vec n) x ts
    | (sum.inr 0) _ _ := false
    | (sum.inr (n+1)) x (conj m t ts) := var_in_term atm x t ∨ var_in_term (vec n) x ts

def var_in_formula : ℕ → formula L → Prop
    | x (equal t t') := var_in_term L atm x t ∨ var_in_term L atm x t'
    | x (atomic n r ts) := var_in_term L (vec n) x ts
    | x (imp f f') := var_in_formula x f ∨ var_in_formula x f'
    | x (not f) := var_in_formula x f
    | x (all n f) := x = n ∨ var_in_formula x f

def var_in_pairs : ℕ → list (nat × term L atm) → Prop
    | x [] := false
    | x ((n, t) :: pairs) := (var_in_term L atm) x t ∨ var_in_pairs x pairs


def max_var_in_term : ∀ n, term L n → ℕ 
    | atm (var L n) := n
    | atm (const c) := 0
    | atm (apply n f ts) := max_var_in_term (vec n) ts
    | (sum.inr 0) _ := 0
    | (sum.inr (n+1)) (conj L t ts) := max (max_var_in_term atm t) (max_var_in_term (vec n) ts)

def max_var_in_pairs : list (ℕ × term L atm) → ℕ
    | [] := 0
    | ((n, t) :: pairs) := max (max_var_in_term L atm t) (max_var_in_pairs pairs)

def max_var_in_formula : formula L → ℕ 
    | (equal t t') := max (max_var_in_term L atm  t) (max_var_in_term L atm t')
    | (atomic n r ts) := max_var_in_term L (vec n) ts
    | (imp f f') := max (max_var_in_formula f) (max_var_in_formula f')
    | (not f) := max_var_in_formula f
    | (all n f) := max n (max_var_in_formula f)

def var_not_in : formula L → list (ℕ × term L atm) → ℕ 
    | f pairs := 1 + (max (max_var_in_formula L f) (max_var_in_pairs L pairs))

def free_pairs : formula L → list (ℕ × term L atm) → list (ℕ × term L atm)
    | f pairs := let fv := free_vars_formula L f in list.filter (λ p : ℕ × term L atm, p.fst ∈ fv) pairs

instance var_in_decidable : ∀ n pairs f, decidable (var_in_formula L n f ∨ var_in_pairs L n pairs) := 
begin
    intros n pairs f,
    admit
end


def substitute_formula : formula L → list (nat × term L atm) → formula L
    | (equal t t') pairs := equal (substitute_term L atm t pairs) (substitute_term L atm t' pairs)
    | (atomic n r t) pairs := atomic n r (substitute_term L (vec n) t pairs) 
    | (imp f f') pairs := imp (substitute_formula f pairs) (substitute_formula f' pairs)
    | (not f) pairs := not (substitute_formula f pairs)
    | (all n f) pairs := if var_in_formula L n f ∨ var_in_pairs L n pairs then let n' := var_not_in L f (free_pairs L f pairs) in all n' (substitute_formula f ((n, var L n') :: pairs)) else all n (substitute_formula f (free_pairs L f pairs))


def vec_length_n_diff_two : ∀ n, ℕ →  term L (vec n)
    | 0 hd := nil L
    | (n+1) hd := conj n (var L hd) (vec_length_n_diff_two n (hd+2))



def even_vec := λ n, vec_length_n_diff_two L n 0
def odd_vec := λ n, vec_length_n_diff_two L n 1


def axm_eq' : ∀ m, formula L → formula L
    | 0 f := (((var L 0) ≍ (var L 1)) ⟾ f)
    | (m+1) f := axm_eq' m (((var L (2 * (m + 1))) ≍ (var L (2 * (m + 1) + 1))) ⟾ f)

def axm_eq_4 : ∀ n, L.functions n → formula L
    | 0 f := ((apply 0 f (nil L)) ≍ (apply 0 f (nil L)))
    | (n+1) f := axm_eq' L n ((apply (n+1) f (even_vec L (n+1)) ≍ (apply (n+1) f (odd_vec L (n+1)))))

def axm_eq_5 : ∀ n, L.relations n → formula L
    | 0 r := ((atomic 0 r (nil L)) ⇔ (atomic 0 r (nil L)))
    | (n+1) r := axm_eq' L n ((atomic (n+1) r (even_vec L (n+1))) ⇔ (atomic (n+1) r (odd_vec L (n+1))))

inductive prf : list (formula L) → formula L → Type
    | axm : ∀ a, prf [a] a
    | mp : ∀ axm axm' f g, prf axm (imp f g) → prf axm' f → prf (axm ++ axm') g
    | gen : ∀ axm f v, ¬ (v ∈ (free_vars_formula L f)) → prf axm f → prf axm (all v f)
    | imp1 : ∀ f g, prf [] (f ⟾ (g ⟾ f))
    | imp2 : ∀ f g h, prf [] (f ⟾ (g ⟾ h) ⟾ ((f ⟾ g) ⟾ (f ⟾ h)))
    | cp : ∀ f g,  prf [] (((not f) ⟾ (not g)) ⟾ (g ⟾ f))
    | all1 : ∀ f v t, prf [] ((all v f) ⟾ (substitute_formula L f [(v,t)]))
    | all2 : ∀ f v, ¬ v ∈ (free_vars_formula L f) → prf [] (f ⟾ all v f)
    | all3 : ∀ f g v, prf [] ((all v (f ⟾ g) ⟾ ((all v f) ⟾ (all v g))))
    | eq1 : prf [] ((var L 0) ≍ (var L 0))
    | eq2 : prf [] (( (var L 0) ≍ (var L 1)) ⟾ ((var L 1) ≍ (var L 0)))
    | eq3 : prf [] (((var L 0) ≍ (var L 1)) ⟾ (((var L 1) ≍ (var L 2)) ⟾ ((var L 0) ≍ (var L 2))))
    /- the following two axioms are examples standing in for the more general equality axioms that need to be generated for n-ary relations and functions;
            
            x0 = x1 ⇒ … ⇒ x2n-2 = x2n-1 ⇒ (R(x0, x2, …, x2n-2) ⇔ R(x1, x3, …, x2n-1))  and
            x0 = x1 ⇒ … ⇒ x2n-2 = x2n-1 ⇒ f(x0, x2, …, x2n-2) = f(x1, x3, …, x2n-1)
            
            src http://r6.ca/Goedel/goedel1.html
            -/
    | eq4 : ∀ n, ∀  r : L.functions n, prf [] (axm_eq_4 L n r)
    | eq5 : ∀ n, ∀ f : L.relations n, prf [] (axm_eq_5 L n f)
 
 /-exact ⟨ λ t1 t2, prod.lex nat.lt nat.lt (sizeof t1.fst, sizeof t1.snd) (sizeof t2.fst, sizeof t2.snd)-/