structure Language := 
(relations : Π n : nat, Type) (functions : Π  n : nat, Type)
section
parameter L : Language

/- preterm n is a partially applied term. if applied to n terms, it becomes a term -/
inductive preterm : ℕ → Type 
| var : ℕ → preterm 0
| func : ∀ {n : nat}, L.functions n → preterm n
| apply : ∀ {n : nat}, preterm (n + 1) → preterm 0 → preterm n
open preterm
def term := preterm 0

/- raise_depth_term _ t n m raises variables in t which are at least m by n -/
def raise_depth_term : ∀ {l}, preterm l → ℕ → ℕ → preterm l
| _ (var L k) n m := if m ≤ k then var (k+m) else var k
| _ (func f) n m := func f
| _ (apply t1 t2) n m := apply (raise_depth_term t1 n m) (raise_depth_term t2 n m)

/- substitute_term t s n substitutes s for (var n) and reduces the level of all variables above n by 1 -/
def substitute_term : ∀ {l}, preterm l → term → ℕ → preterm l
| _ (var L k) s n := if k < n then var k else if k > n then var (k-1) else s
| _ (func f) s n := func f
| _ (apply t1 t2) s n := apply (substitute_term t1 s n) (substitute_term t2 s n)

/- preformula n is a partially applied formula. if applied to n terms, it becomes a formula -/
inductive preformula : ℕ → Type 
| false : preformula 0
| equal : term → term → preformula 0
| rel : ∀ {n : nat}, L.relations n → preformula n
| apprel : ∀ {n : nat}, preformula (n + 1) → term → preformula n
| imp : preformula 0 → preformula 0 → preformula 0
| all : preformula 0 → preformula 0
open preformula
def formula := preformula 0

def raise_depth_formula : ∀ {l}, preformula l → ℕ → ℕ → preformula l
| _ (false L) n m := false
| _ (equal t1 t2) n m := equal (raise_depth_term t1 n m) (raise_depth_term t2 n m)
| _ (rel R) n m := rel R
| _ (apprel f t) n m := apprel (raise_depth_formula f n m) (raise_depth_term t n m)
| _ (imp f1 f2) n m := imp (raise_depth_formula f1 n m) (raise_depth_formula f2 n m)
| _ (all f) n m := all (raise_depth_formula f n (m+1))

def substitute_formula : ∀ {l}, preformula l → term → ℕ → preformula l
| _ (false L) s n := false
| _ (equal t1 t2) s n := equal (substitute_term t1 s n) (substitute_term t2 s n)
| _ (rel R) s n := rel R
| _ (apprel f t) s n := apprel (substitute_formula f s n) (substitute_term t s n)
| _ (imp f1 f2) s n := imp (substitute_formula f1 s n) (substitute_formula f2 s n)
| _ (all f) s n := all (substitute_formula f s (n+1))

end
