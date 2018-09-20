/- 9/20/18 
    Preliminary definitions and some functions for working with languages and first-order logic.
    Much of the structure and methods are taken from Russell O'Connor's proof of Goedel's incompleteness theorem, at http://r6.ca/Goedel/goedel1.html
    Andrew Tindall-/

structure Language := 
    language :: (relations : Π n : nat, Type) (functions : Π  n : nat, Type)
variable L : Language


inductive term  : Π n, Type 
    | nil : term 1
    | var : ℕ → term 0
    | conj : ∀ n, term 0 → term n → term (n + 1)
    | apply : ∀ (n : nat) (f : L.functions n), term (n+1) → term 0
open term


def term_sizeof :Π n, term L n → ℕ 
    | 0 (var L n) := 0
    | 0 (apply n f ts) :=  n + 2 + term_sizeof (n+1) ts
    | n (conj m t ts) := 1 + term_sizeof 0 t + term_sizeof m ts
    | 1 (nil L) := 0
instance term_has_sizeof { n: nat}  : has_sizeof (term L n) := ⟨ term_sizeof L n ⟩ 


inductive formula : Type 
    | equal : term L 0 → term L 0 → formula
    | atomic : ∀ (n : nat) (r : L.relations n), term L (n+1) → formula 
    | imp : formula → formula → formula
    | not : formula → formula
    | all : ℕ → formula → formula
open formula

def andf := λ f g, not (imp f (not g))

reserve infix `⟾`:10
infix ⟾ := imp

reserve infix `⟺`:15
infix ⟺ := λ f g, andf (f ⟾ g) (g ⟾ f)

reserve infix `≍`:20
infix ≍ := equal

def free_vars_term : Π n, (term L n) → list ℕ 
    | 1 _ := []
    | 0 (var L n) := [n]
    | 0 (apply n f ts) := free_vars_term (n+1) ts
    | (n+1) (conj L t ts) := list.union (free_vars_term 0 t) (free_vars_term n ts)

def free_vars_formula : formula L → list ℕ 
    | (equal t1 t2) := list.union (free_vars_term L 0 t1) (free_vars_term L 0 t2)
    | (atomic n r ts) := free_vars_term L (n+1) ts
    | (imp f1 f2) := list.union (free_vars_formula f1) (free_vars_formula f2)
    | (not f) := free_vars_formula f
    | (all n f) := list.filter (≠ n) (free_vars_formula f)


lemma lt_add : ∀ (n m k : ℕ), n < m → n < k + m:= begin {intros n m k n_lt_m, induction k, rw zero_add,exact n_lt_m, rw nat.succ_add, apply nat.lt_succ_of_lt,exact k_ih} end
lemma add_lt : ∀ (n m k : ℕ), n < m → n < m + k := begin {intros n m k n_lt_m, induction k, rw add_zero,exact n_lt_m, rw nat.add_comm, rw nat.succ_add, apply nat.lt_succ_of_lt, rw nat.add_comm, exact k_ih} end

def substitute_term : Π (n : nat), term L n → list (nat × term L 0) → term L n
    | 1 a b := nil L
    | 0 (var L n) [] := var L n
    | 0 (var L n) ((m, t) :: pairs) := if n = m then t else substitute_term 0 (var L n) pairs
    | 0 (apply n f ts) pairs := have n + (2 + term_sizeof L (n + 1) ts) < 1 + term_sizeof L 0 (apply n f ts), from
        begin
        simp [term_sizeof],
        apply add_lt_add_left,
            have l : ∀ a: nat, a < 1 + a, by {intro a,rw add_comm, rw nat.add_one, apply nat.lt_succ_self},
            apply l,
        end,
    apply n f (substitute_term (n+1) ts pairs)
    | n (conj m t ts) pairs := have 1 + term_sizeof L 0 t < m + (2 + term_sizeof L (m + 1) (conj m t ts)), from 
        begin
            simp [term_sizeof],
            apply lt_add, apply lt_add, apply lt_add,
            apply add_lt_add_right,
            admit,
        end, have 1 + term_sizeof L m ts < 2 + term_sizeof L (m + 1) (conj m t ts), from 
            begin 
                simp [term_sizeof], apply add_lt_add_left, apply lt_add_of_pos_right, admit
            end,
    conj m (substitute_term 0 t pairs) (substitute_term m ts pairs)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf psigma.sizeof⟩]}

def var_in_term : ∀ n, ℕ → term L n → Prop
    | 0 x (var L y) := x = y
    | 0 x (apply n f ts) := var_in_term (n+1) x ts
    | (n+1) x (conj m t ts) := var_in_term 0 x t ∨ var_in_term n x ts
    | 1 x (nil L) := false

def var_in_formula : ℕ → formula L → Prop
    | x (equal t t') := var_in_term L 0 x t ∨ var_in_term L 0 x t'
    | x (atomic n r ts) := var_in_term L (n+1) x ts
    | x (imp f f') := var_in_formula x f ∨ var_in_formula x f'
    | x (not f) := var_in_formula x f
    | x (all n f) := x = n ∨ var_in_formula x f

def var_in_pairs : ℕ → list (nat × term L 0) → Prop
    | x [] := false
    | x ((n, t) :: pairs) := var_in_term L 0 x t ∨ var_in_pairs x pairs


def max_var_in_term : ∀ n, term L n → ℕ 
    | 1 _ := 0
    | 0 (var L n) := n
    | 0 (apply n f ts) := max_var_in_term (n+1) ts
    | (n+1) (conj L t ts) := max (max_var_in_term 0 t) (max_var_in_term n ts)

def max_var_in_pairs : list (ℕ × term L 0) → ℕ
    | [] := 0
    | ((n, t) :: pairs) := max (max_var_in_term L 0 t) (max_var_in_pairs pairs)

def max_var_in_formula : formula L → ℕ 
    | (equal t t') := max (max_var_in_term L 0  t) (max_var_in_term L 0 t')
    | (atomic n r ts) := max_var_in_term L (n+1) ts
    | (imp f f') := max (max_var_in_formula f) (max_var_in_formula f')
    | (not f) := max_var_in_formula f
    | (all n f) := max n (max_var_in_formula f)

def var_not_in : formula L → list (ℕ × term L 0) → ℕ 
    | f pairs := 1 + (max (max_var_in_formula L f) (max_var_in_pairs L pairs))

def free_pairs : formula L → list (ℕ × term L 0) → list (ℕ × term L 0)
    | f pairs := let fv := free_vars_formula L f in list.filter (λ p : ℕ × term L 0, p.fst ∈ fv) pairs

instance var_in_decidable : ∀ n pairs f, decidable (var_in_formula L n f ∨ var_in_pairs L n pairs) := 
begin
    intros n pairs f,
    admit
end



def substitute_formula : formula L → list (nat × term L 0) → formula L
    | (equal t t') pairs := equal (substitute_term L 0 t pairs) (substitute_term L 0 t' pairs)
    | (atomic n r t) pairs := atomic n r (substitute_term L (n+1) t pairs) 
    | (imp f f') pairs := imp (substitute_formula f pairs) (substitute_formula f' pairs)
    | (not f) pairs := not (substitute_formula f pairs)
    | (all n f) pairs := if var_in_formula L n f ∨ var_in_pairs L n pairs then let n' := var_not_in L f (free_pairs L f pairs) in all n' (substitute_formula f ((n, var L n') :: pairs)) else all n (substitute_formula f (free_pairs L f pairs))

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
    | eq4 : ∀ r : L.relations 2, prf [] (((var L 0) ≍ (var L 1)) ⟾ 
                                        (((var L 2) ≍ (var L 3)) ⟾ 
                                            ((atomic 2 r (conj 2 (var L 0) (conj 1 (var L 2) (nil L)))) ⟺ (atomic 2 r (conj 2 (var L 1) (conj 1 (var L 3) (nil L)))))))
    | eq5 : ∀ f : L.functions 2, prf [] (((var L 0) ≍ (var L 1)) ⟾ 
                                        (((var L 2) ≍ (var L 3)) ⟾ 
                                            ((apply 2 f (conj 2 (var L 0) (conj 1 (var L 2) (nil L)))) ≍ (apply 2 f (conj 2 (var L 1) (conj 1 (var L 3) (nil L)))))))
 
 /-exact ⟨ λ t1 t2, prod.lex nat.lt nat.lt (sizeof t1.fst, sizeof t1.snd) (sizeof t2.fst, sizeof t2.snd)-/