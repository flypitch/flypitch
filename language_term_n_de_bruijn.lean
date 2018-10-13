/- 9/20/18 
    Preliminary definitions and some functions for working with languages and first-order logic.
    Much of the structure and methods are taken from Russell O'Connor's proof of Goedel's incompleteness theorem, at http://r6.ca/Goedel/goedel1.html
    Andrew Tindall-/

/- 2018-09-21T13:12:55
   Added some proof rules more closely reflecting rules of deduction in Prop
   We should double-check that the additional constructors true, false, and and or have been taken care of appropriately in the implementation of de Bruijn indices.
   ---Jesse -/

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
    | true : formula
    | false : formula
    | equal : term L atm → term L atm → formula
    | atomic : ∀ (n : nat) (r : L.relations n), term L (vec n) → formula 
    | and : formula → formula → formula
    | or : formula → formula → formula
    | imp : formula → formula → formula
    | not : formula → formula
    | all : formula → formula
open formula

def andf := λ (f : formula L) g, not (imp f (not g))

reserve infix `⟾`:10
infix ⟾ := imp

reserve infix `⇔`:15
local infix ⇔ := λ (f : formula L) g, andf L (f ⟾ g) (g ⟾ f)

reserve infix `≍`:20
infix ≍ := equal

def free_vars_term : Π n, ℕ → (term L n) → list ℕ 
    | atm m (var L k) :=if k > m then [k - m] else []
    | atm m (const c) := []
    | atm m (apply n f ts) := free_vars_term (vec n) m ts
    | (sum.inr 0) _ _ := []
    | (sum.inr (n+1)) m (conj _ t ts) := list.union (free_vars_term atm m t) (free_vars_term (vec n) m ts)

def free_vars_formula : ℕ → formula L → list ℕ 
    | m (equal t1 t2) := list.union (free_vars_term L atm m t1) (free_vars_term L atm m t2)
    | m (atomic n r ts) := free_vars_term L (vec n) m ts
    | m (and t1 t2) := list.union(free_vars_formula m t1) (free_vars_formula m t2)
    | m (or t1 t2) := list.union(free_vars_formula m t1) (free_vars_formula m t2)
    | m (imp f1 f2) := list.union (free_vars_formula m f1) (free_vars_formula m f2)
    | m (not f) := free_vars_formula m f
    | m (all  f) := free_vars_formula (m+1) f
    | m (false L) := []
    | m (true L) := []


def raise_depth_term : ∀ n, term L n → ℕ  → term L n
    | atm (var L n) m := var L (n+m)
    | atm (const c) _ := const c
    | atm (apply n f ts) m := apply n f (raise_depth_term (vec n) ts m)
    | (sum.inr 0) _ _ := nil L
    | (sum.inr (n+1)) (conj _ t ts) m := conj n (raise_depth_term atm t m) (raise_depth_term (vec n) ts m)
def raise_depth_formula : formula L → ℕ → formula L
    | (equal t1 t2) m := equal (raise_depth_term L atm t1 m) (raise_depth_term L atm t2 m)
    | (atomic n r ts) m := atomic n r (raise_depth_term L (vec n) ts m)
    | (and t1 t2) m :=  and (raise_depth_formula t1 m) (raise_depth_formula t2 m)
    | (or t1 t2) m :=  or (raise_depth_formula t1 m) (raise_depth_formula t2 m)    
    | (imp f1 f2) m := imp (raise_depth_formula f1 m) (raise_depth_formula f2 m)
    | (not f) m := not (raise_depth_formula f m)
    | (all f) m := all (raise_depth_formula f m)
    | (false L) m := (false L)
    | (true L) m := (true L)

def lower_depth_term : ∀ n, term L n → ℕ  → term L n
    | atm (var L n) m := var L (n-m)
    | atm (const c) _ := const c
    | atm (apply n f ts) m := apply n f (lower_depth_term (vec n) ts m)
    | (sum.inr 0) _ _ := nil L
    | (sum.inr (n+1)) (conj _ t ts) m := conj n (lower_depth_term atm t m) (lower_depth_term (vec n) ts m)
def lower_depth_formula : formula L → ℕ → formula L
    | (equal t1 t2) m := equal (lower_depth_term L atm t1 m) (lower_depth_term L atm t2 m)
    | (atomic n r ts) m := atomic n r (lower_depth_term L (vec n) ts m)
    | (and t1 t2) m :=  and (lower_depth_formula t1 m) (lower_depth_formula t2 m)
    | (or t1 t2) m :=  or (lower_depth_formula t1 m) (lower_depth_formula t2 m)    
    | (imp f1 f2) m := imp (lower_depth_formula f1 m) (lower_depth_formula f2 m)
    | (not f) m := not (lower_depth_formula f m)
    | (all f) m := all (lower_depth_formula f m)
    | (false L) m := (false L)
    | (true L) m := (true L)


lemma lt_add : ∀ (n m k : ℕ), n < m → n < k + m:= begin {intros n m k n_lt_m, induction k, rw zero_add,exact n_lt_m, rw nat.succ_add, apply nat.lt_succ_of_lt,exact k_ih} end
lemma add_lt : ∀ (n m k : ℕ), n < m → n < m + k := begin {intros n m k n_lt_m, induction k, rw add_zero,exact n_lt_m, rw nat.add_comm, rw nat.succ_add, apply nat.lt_succ_of_lt, rw nat.add_comm, exact k_ih} end


def substitute_term : Π (n : term_param), term L n → nat × term L atm → nat  → term L n
    | atm (var L n) (x, t') m := if (x+m) = n then raise_depth_term L atm t' m else var L n
    | atm (const c) _ _ := const c
    | atm (apply n f ts) (x,t') m := have term_sizeof L (sum.inr n) ts < term_sizeof L atm (apply n f ts), from 
        begin 
            simp [term_sizeof],
            apply lt_add,
            apply nat.lt_add_of_pos_right,
            apply nat.zero_lt_succ
        end,
     apply n f (substitute_term (sum.inr n) ts (x,t') m)
    | (sum.inr 0) _ _ _ := nil L
    | (sum.inr (n+1)) (conj k t ts) (x,t') m := have term_sizeof L atm t < term_sizeof L (sum.inr (k + 1)) (conj k t ts), from
        begin
            simp [term_sizeof, nat.succ_add],
            apply nat.lt_of_succ_le, apply nat.succ_le_succ,
            apply nat.le_add_right
        end,
        have term_sizeof L (vec k) ts < term_sizeof L (sum.inr (k + 1)) (conj k t ts), from
        begin
            simp [term_sizeof, nat.succ_add],
            apply nat.lt_of_succ_le, apply nat.succ_le_succ,
            apply nat.le_add_left
        end,
    conj n (substitute_term atm t (x,t') m) (substitute_term (vec n) ts (x,t') m)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf psigma.sizeof⟩]}



/- I think we don't need these but I didn't want to delete them yet 

def var_in_term : ∀ n, ℕ → ℕ → term L n → Prop
    | atm x m (var L y) := (x+m) = y
    | atm _ _ (const c) := false
    | atm x m (apply n f ts) := var_in_term (vec n) x m ts
    | (sum.inr 0) _ _ _ := false
    | (sum.inr (n+1)) x m (conj _ t ts) := var_in_term atm x m t ∨ var_in_term (vec n) x m ts

def var_in_formula : ℕ → ℕ → formula L → Prop
    | x m (equal t t') := var_in_term L atm x m t ∨ var_in_term L atm x m t'
    | x m (atomic n r ts) := var_in_term L (vec n) x m ts
    | x m (imp f f') := var_in_formula x m f ∨ var_in_formula x m f'
    | x m (not f) := var_in_formula x m f
    | x m (all f) := var_in_formula x (m+1) f
-/


def substitute_formula : formula L → (nat × term L atm) → ℕ → formula L
    | (equal t t') pair m := equal (substitute_term L atm t pair m) (substitute_term L atm t' pair m)
    | (atomic n r t) pair m := atomic n r (substitute_term L (vec n) t pair m) 
    | (and t1 t2) pair m :=  and (substitute_formula t1 pair m) (substitute_formula t2 pair m)
    | (or t1 t2) pair m :=  or (substitute_formula t1 pair m) (substitute_formula t2 pair m)    
    | (imp f f') pair m := imp (substitute_formula f pair m) (substitute_formula f' pair m)
    | (not f) pair m := not (substitute_formula f pair m)
    | (all f) pair m := substitute_formula f pair (m+1)
    | (false L) pair m := (false L)
    | (true L) pair m := (true L)




/-these are helper functions for constructing the family of extensionality axioms. even_vec n creates the term ⟦ var 0, var 2, ... var 2n ⟧ and odd_vec n creates ⟦ var 1, ... var 2n+1 ⟧ -/

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

-- L.true must be interpreted as true --- need to have reified true for soundness

inductive prf : list (formula L) → formula L → Type
    | true_intro : ∀ as, prf as (true L) -- true is vacuously provable
    | false_elim : ∀ a, prf [false L] a  -- principle of explosion
    | not_elim : ∀ a, prf [not a] (a ⟾ (false L))
    | not_intro :∀ a, prf [a ⟾ false L] (not a)
    | and_eliml : ∀ a b, prf [formula.and a b] a -- if we know A ∧ B, then we know A 
    | and_elimr : ∀ a b, prf [formula.and a b] b -- if we know A ∧ B, then we know B
    | and_intro : ∀ as, prf as (as.foldr (formula.and) (true L)) -- if A1...An are known, then true ∧ A1 ∧ ... ∧ An is provable (and true ∧ B → B) by modus ponens and and_elim
    | or_intro : ∀ a b, prf [a] (formula.or a b) -- if we know A is true, then for any B, A ∨ B is true.
    | axm : ∀ a, prf [a] (true L ⟾ a) -- equivalent to O'Connor's axm by MP
    | mp : ∀ axm axm' f g, prf axm (imp f g) → prf axm' f → prf (axm ++ axm') g
--    | gen : ∀ axm f, prf axm f → prf axm (all (raise_depth_formula L f 1)) --- this follows from all2 and using and_intro to move axm to the right
    | imp1 : ∀ f g, prf [] (f ⟾ (g ⟾ f))
    | imp2 : ∀ f g h, prf [] (f ⟾ (g ⟾ h) ⟾ ((f ⟾ g) ⟾ (f ⟾ h)))
--    | cp : ∀ f g,  prf [] (((not f) ⟾ (not g)) ⟾ (g ⟾ f)) --- until we implement tautology reflection, we should just have double-negation elimination outright
    | dne : ∀ f, prf [] ((not (not f)) ⟾ f)
    | forall_elim : ∀ f t, prf [] ((all f) ⟾ (raise_depth_formula L (substitute_formula L f (0,t) 0)) 1)
    | all2 : ∀ f g, prf [] ((all (f ⟾ g) ⟾ ((all f) ⟾ (all g)))) -- TODO: this seems fishy --- why aren't we able to only quantify over _some_ of the free variables, if we're allowing open variables in the proof system in the first place?
    | eq1 : prf [] ((var L 0) ≍ (var L 0))
    | eq2 : prf [] (( (var L 0) ≍ (var L 1)) ⟾ ((var L 1) ≍ (var L 0)))
    | eq3 : prf [] (((var L 0) ≍ (var L 1)) ⟾ (((var L 1) ≍ (var L 2)) ⟾ ((var L 0) ≍ (var L 2))))
    /- the following two axioms are general equality axioms that are generated for n-ary relations and functions;
            
            x0 = x1 ⇒ … ⇒ x2n-2 = x2n-1 ⇒ (R(x0, x2, …, x2n-2) ⇔ R(x1, x3, …, x2n-1))  and
            x0 = x1 ⇒ … ⇒ x2n-2 = x2n-1 ⇒ f(x0, x2, …, x2n-2) = f(x1, x3, …, x2n-1)
            
            src http://r6.ca/Goedel/goedel1.html
            -/
    | eq4 : ∀ n, ∀  r : L.functions n, prf [] (axm_eq_4 L n r)
    | eq5 : ∀ n, ∀ f : L.relations n, prf [] (axm_eq_5 L n f)
