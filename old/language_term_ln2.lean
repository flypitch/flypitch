/-
Another implementation of locally nameless representation, more faithful to Chaugeuraud's specification. Thank you to Floris for the code underlying preterms and preformulas. ---Jesse 2018-10-15T19:59:39
-/

structure Language := 
(relations : Π n : nat, Type) (functions : Π  n : nat, Type)
section
parameter L : Language

/-- preterm n is a partially applied term. If applied to n terms, it becomes a term. --/
inductive preterm  : ℕ → Type 
| bvar : ℕ → preterm 0
| fvar : ℕ → preterm 0 -- this should be fine; later we can pretty-print free variables with the indices as the underscores.
| func : ∀ {n : nat}, L.functions n → preterm n
| apply : ∀ {n : nat}, preterm (n + 1) → preterm 0 → preterm n

open preterm
def term := preterm 0

/-- Given a preterm, return a list of free variables which occur in it--/
def free_vars_preterm : Π n : ℕ, preterm n → list ℕ
| _ (bvar L k) := []
| _ (fvar L s) := [s]
| _ (@func L _ f) := []
| _ (@apply L n t1 t2) := (free_vars_preterm (n+1) t1 ∪ free_vars_preterm 0 t2)

/-- Given a preterm, return a list of bound variables which occur in it--/
def bound_vars_preterm : Π n : ℕ, preterm n → list ℕ
| _ (bvar L k) := [k]
| _ (fvar L s) := []
| _ (@func L _ f) := []
| _ (@apply L n t1 t2) := (free_vars_preterm (n+1) t1 ∪ free_vars_preterm 0 t2)

def free_vars_term : term → list ℕ := free_vars_preterm 0

def bound_vars_term : term → list ℕ := bound_vars_preterm 0

-- lemma free_var_preterm_coercionl (n : ℕ) (t1 : preterm (n+1)) (t2 : term) : {x : ℕ // x ∈ (free_vars_preterm (n+1) t1)} → {x : ℕ // x ∈ (free_vars_preterm n (apply t1 t2))} := sorry

-- def substitute_preterm : Π n : ℕ, Π (t : preterm n), term → {x : ℕ // x ∈ (free_vars_preterm n t)} → preterm n
-- | _ (bvar L k) t x := (bvar k)
-- | _ (fvar L s) t x := sorry
-- | _ (@func L _ f) t x := (func f)
-- | _ (@apply L n t1 t2) t x := sorry
end

section

parameter L : Language
/- preformula n is a partially applied formula. if applied to n terms, it becomes a formula -/
inductive preformula : ℕ → Type 
| true : preformula 0
| false : preformula 0
| equal : (term L)  → (term L) → preformula 0
| rel : ∀ {n : nat}, L.relations n → preformula n
| apprel : ∀ {n : nat}, preformula (n + 1) → (term L) → preformula n
| imp : preformula 0 → preformula 0 → preformula 0
| all : preformula 0 → preformula 0

open preformula
def formula := preformula 0

def free_vars_preformula : Π n : ℕ, preformula n → list ℕ
| _ (true L) := []
| _ (false L) := []
| _ (equal t1 t2) := free_vars_term L t1 ∪ free_vars_term L t2
| _ (@rel L n R) := []
| _ (@apprel L n ψ t) := free_vars_preformula _ ψ ∪ free_vars_term L t
| _ (imp ϕ ψ) := free_vars_preformula _ ϕ ∪ free_vars_preformula _ ψ
| _ (all ψ) := free_vars_preformula _ ψ

def bound_vars_preformula : Π n : ℕ, preformula n → list ℕ 
| _ (true L) := []
| _ (false L) := []
| _ (equal t1 t2) := bound_vars_term L t1 ∪ bound_vars_term L t2
| _ (@rel L n R) := []
| _ (@apprel L n ψ t) := bound_vars_preformula _ ψ ∪ bound_vars_term L t
| _ (imp ϕ ψ) := bound_vars_preformula _ ϕ ∪ bound_vars_preformula _ ψ
| _ (all ψ) := bound_vars_preformula _ ψ

def free_vars_formula : formula → list ℕ := free_vars_preformula 0
def bound_vars_formula : formula → list ℕ := bound_vars_preformula 0



-- def fresh_var : list ℕ → ℕ := λ xs, xs.foldr max 0
/- OPERATIONS ON LOCALLY NAMELESS FORMULAS -/
/- Variable opening -/
-- I quote:
-- With the named representation, an abstraction takes the form “λx. t”. To investigate
-- the body of this abstraction, we simply works with the term t. With the locally nameless
-- representation, an abstraction has the form “abs t” and it is our responsibility to provide
-- a fresh name x to open the abstraction. The result of applying the variable opening oper-
-- ation to t and x is a term, written t x , that describes the body of the abstraction “abs t”.
-- More precisely, given an abstraction “abs t” and a variable name x that does not appear
-- in t, the term t x is a copy of t in which all the bound variables referring to the outer
-- abstraction of “abs t” have been replaced with the free variable “fvar x”. For example,
-- consider the abstraction “abs (app (abs (app (bvar 0) (bvar 1))) (bvar 0))”; the opening of
-- its body with the name x is the term “app (abs (app (bvar 0) (fvar x)))(fvar x) ”.
-- The implementation of variable opening needs to traverse a term recursively, and
-- find all the leaves of the form “bvar i” whose index i is equal to the number of abstrac-
-- tions enclosing that variable. Variable opening is thus defined in terms of a recursive
-- function, written “{k → x} t”, that keeps track of the number k of abstractions that
-- have been passed by. Initially, the value of k is 0, so variable opening is defined as:
-- t x ≡ {0 → x} t

-- The value of k is then incremented each time an abstraction is traversed. When reaching
-- a bound variable with index i, the value of i is compared against the current value of k.
-- If i is equal to k, then the bound variable is replaced with the free variable named x,
-- otherwise it is unchanged. Note that free variables already occurring in the term are
-- never affected by a variable opening operation.
-- We will need this to perform generalization of constants.

-- def var_open_term : ℕ → term L → term L
-- | k (preterm.bvar _ i) := if (i = k)
-- then preterm.fvar _ (fresh_var (free_vars_term _ (preterm.bvar L i)))
-- else (preterm.bvar _ i)
-- | k (preterm.fvar _ y) := preterm.fvar _ y
-- | k (preterm.func f) := preterm.func f
-- | k (preterm.apply (t1 : preterm L 1) (t2 : preterm L 0) := preterm.apply (var_open_term k t1) (var_open_term k t2)

--- funnily enough, if you try to do this for *just* terms, like above, the equation compiler complains about well-founded recursion. But as you see below, there's *no* problem if we do it for all preterms

def fresh_var : list ℕ → ℕ := λ xs, (xs.foldr max 0) + 1

def var_open_preterm : Π n : ℕ, ℕ → preterm L n  → preterm L n -- first ℕ is the preterm level, second is the bound index we're opening
| 0 k (preterm.bvar L i) := if (i = k)
then preterm.fvar _ (fresh_var (free_vars_term _ (preterm.bvar L i)))
else (preterm.bvar _ i)
| 0 k (preterm.fvar L y) := preterm.fvar _ y
| n k (preterm.func f) := preterm.func f
| n k (preterm.apply (t1 : preterm L (n+1)) (t2 : preterm L 0)) := preterm.apply (var_open_preterm (n+1) k t1) (var_open_preterm 0 k t2)
 
/- opens the outermost abstraction of an n-preformula with a free variable fvar k-/
def var_open_preformula : Π (n : ℕ), ℕ → preformula n → preformula n
| 0 k (true L) := true
| 0 k (false L) := false
| 0 k (equal t1 t2) := equal (var_open_preterm _ k t1) (var_open_preterm _ k t2)
| 0 k (imp ϕ ψ) := imp (var_open_preformula 0 k ϕ) (var_open_preformula 0 k ψ)
| 0 0 (all ϕ) := var_open_preformula 0 1 ϕ -- careful! we only strip the quantifier and increase the count when we hit the _first_ quantifier, after that, only increase the count
| 0 (n+1) (all ϕ) := (all (var_open_preformula 0 (n+1) ϕ))
| n k (rel R) := (rel R)
| n k (apprel (ψ : preformula (n+1)) t) := apprel (var_open_preformula (n+1) k ψ) (var_open_preterm 0 k t)





/-Variable closing-/
-- I quote: Symmetrically to variable opening, we may want to build an abstraction given its
-- body. With the named representation, we consider a term t and a name x, and we
-- simply build the abstraction “λx. t”. All the variables named x are abstracted, except
-- those that already appear below an abstraction named x. With the locally nameless
-- representation, we consider a term t and a name x to be abstracted in t, and we
-- build a term, written \x t, by applying the variable closing operation to t and x. All
-- the variables named x occurring in t are abstracted, without exception (indeed, no
-- shadowing is possible with the locally nameless syntax). The abstraction may then be
-- constructed as “abs ( \x t)”. More precisely, the term \x t is a copy of t in which all the
-- free variables named x have been replaced with a bound variable. The indices of those
-- variables are chosen in such a way that all the bound variables introduced are pointing
-- towards the outer abstraction of “abs ( \x t)”.
-- The implementation of variable closing follows a pattern similar to the implemen-
-- tation of variable opening. Its implementation is based on a recursive function, written
-- “{k ← x} t”, that keeps track of the number k of abstractions that have been passed by.
-- Again, the value of k is 0 initially and it is incremented at each abstraction. Variable
-- closing is defined as follows:
-- \x
-- t ≡ {0 ← x} t
-- When the recursive function reaches a free variable with name y, it compares the name
-- y with the name x. If the two names match, then the free variable y is replaced with
-- a bound variable of index k, otherwise it is left unchanged. Note that bound variables
-- already occurring in the term are never affected by variable closing.



def var_close_preterm : Π n : ℕ, ℕ → preterm L n  → preterm L n -- first ℕ is the preterm level, second is the open index we're closing
| 0 k (preterm.fvar L i) := if (i = k)
then preterm.bvar _ k
else (preterm.fvar _ i)
| 0 k (preterm.bvar L y) := preterm.fvar _ y
| n k (preterm.func f) := preterm.func f
| n k (preterm.apply (t1 : preterm L (n+1)) (t2 : preterm L 0)) := preterm.apply (var_close_preterm (n+1) k t1) (var_close_preterm 0 k t2)
 
/- wraps an abstraction around an n-preformula, binding a specified free variable-/
def var_close_preformula : Π (n : ℕ), ℕ → preformula n → preformula n
| 0 k (true L) := true
| 0 k (false L) := false
| 0 k (equal t1 t2) := equal (var_close_preterm _ k t1) (var_close_preterm _ k t2)
| 0 k (imp ϕ ψ) := imp (var_close_preformula 0 k ϕ) (var_close_preformula 0 k ψ)
| 0 k (all ϕ) := all (var_close_preformula 0 (k+1) ϕ)
| n k (rel R) := (rel R)
| n k (apprel (ψ : preformula (n+1)) t) := apprel (var_close_preformula (n+1) k ψ) (var_close_preterm 0 k t)

/-***********************************-/

/- LOCALLY CLOSED TERMS -/
-- unfortunately, we need a well-formedness predicate. Again, to quote Chargueraud:
-- As suggested in the previous section, the locally nameless syntax contains objects
-- that do not correspond to any valid λ-term. For instance, “abs 3” is such an improper
-- syntactic object, since the bound variable with index 3 does not refer to any abstraction
-- inside the term. We need to ensure that terms do not contain any such dangling bound
-- variable. We say of well-formed terms that they are locally closed. The purpose of this
-- section is to give a formal characterization of the set of locally closed terms.
-- Two approaches are possible. The first one consists in investigating the term recur-
-- sively, opening every abstraction with a name, and checking that no bound variable is
-- ever reached. The second possible approach relies on an analysis of bound variables,
-- for checking that each bound variable has an index smaller than the number of enclos-
-- ing abstractions. We start by describing the first approach, which is the most helpful
-- for formally reasoning on terms represented in locally nameless style, and study the
-- approach based on indices afterwards.
-- The local closure predicate, written “lc t”, characterizes terms that are locally
-- closed. It is defined using three inductive rules. The first one states that any free
-- variable is locally closed. The second one states that an application is locally closed if
-- its two branches are locally closed. The third and last one states that an abstraction
-- is locally closed if its body opened with some name is itself locally closed. Notice that
-- a bound variable on its own is never locally closed.

-- In practice, we use a slightly different rule to deal with abstractions. In the rule
-- lc-var’, the premise lc (t x ) is required to hold for one single name x. Instead, we are
-- going to require lc (t x ) to hold for cofinitely-many names x. More precisely, we consider
-- that an abstraction “abs t” is locally closed if there exists a finite set of names L such
-- that, for any name x not in L, the term t x is locally closed.

-- The motivation for the cofinite quantification will be discussed in details later on (§4.2)

-- Arthur's talking crazy. I'm going with the counting-of-bound-variables.
end

variable L : Language

def locally_closed_preterm : Π n : ℕ, ℕ → preterm L n → Prop
| 0 k (preterm.bvar L i) := nat.lt i k
| 0 k (preterm.fvar L i) := true
| n k (preterm.func f) := true
| n k (preterm.apply t1 t2) := (locally_closed_preterm (n+1) k t1) ∧ (locally_closed_preterm 0 k t2)

def locally_closed_preformula : Π n : ℕ, ℕ → preformula L n → Prop
| 0 k (preformula.true L) := true
| 0 k (preformula.false L) := tt
| 0 k (preformula.equal t1 t2) := (locally_closed_preterm L 0 k t1) ∧ (locally_closed_preterm L 0 k t2)
| 0 k (preformula.imp ψ ϕ) := (locally_closed_preformula 0 k ψ) ∧ (locally_closed_preformula 0 k ϕ)
| 0 k (preformula.all ψ) := (locally_closed_preformula 0 (k+1) ψ)
| n k (preformula.rel R) := tt
| n k (preformula.apprel ψ t) := (locally_closed_preformula (n+1) k ψ) ∧ (locally_closed_preterm L 0 k t)

-- NOTE: "locally closed" means the same as "well-formed". Therefore, we introduce the following aliases

/-- A well-formed term, by itself, has no bound variables --/
def well_formed_term : term L → Prop := locally_closed_preterm L 0 0

/-- A well-formed formula is a locally closed preformula. Remember the second nat parameter counts the number of quantifiers we have passed.--/
def well_formed_formula : formula L → Prop := locally_closed_preformula L 0 0
/-***********************************-/


/-FREE VARIABLES AND SUBSTITUTION-/
-- Note that we can define the substitution t/x for x not even occuring in a term or formula. In that case, the substitution operation does nothing. If we have to prove this later, it shouldn't be hard.

/-- Given an n-preterm, a term t, and a fvar x, return that n-preterm with all instances of x replaced with t--/
def substitute_preterm : Π n : ℕ, preterm L n → term L → ℕ → preterm L n
| 0 (preterm.bvar L i) t k := preterm.bvar L i
| 0 (preterm.fvar _ i) t k := if i = k then t else (preterm.fvar _ i)
| n (preterm.func f) t k := (preterm.func f)
| n (preterm.apply t1 t2) t k := preterm.apply (substitute_preterm (n+1) t1 t k) (substitute_preterm 0 t2 t k)

/-- Given an n-preformula, a term t, and a fvar x, return that n-preterm with all instances of x replaced with t--/
def substitute_preformula : Π n : ℕ, preformula L n → term L → ℕ → preformula L n
| _ (preformula.true L) _ _ := preformula.true L
| _ (preformula.false L) _ _ := preformula.false L
| _ (preformula.equal t1 t2) t k := preformula.equal (substitute_preterm L 0 t1 t k) (substitute_preterm L 0 t2 t k)
| _ (preformula.rel R) t k := preformula.rel R
| _ (preformula.apprel ϕ s) t k := preformula.apprel (substitute_preformula _ ϕ t k) (substitute_preterm L _ s t k)
| _ (preformula.imp ϕ ψ) t k := preformula.imp (substitute_preformula _ ϕ t k) (substitute_preformula _ ψ t k)
| _ (preformula.all ψ) t k := preformula.all (substitute_preformula _ ψ t k)

/-***********************************-/



/- ignore the rest of this file-/

-- def raise_depth_formula : ∀ {l}, preformula l → ℕ → ℕ → preformula l
-- | _ (true L) n m := true
-- | _ (false L) n m := false
-- | _ (equal t1 t2) n m := equal (raise_depth_term t1 n m) (raise_depth_term t2 n m)
-- | _ (rel R) n m := rel R
-- | _ (apprel f t) n m := apprel (raise_depth_formula f n m) (raise_depth_term t n m)
-- | _ (imp f1 f2) n m := imp (raise_depth_formula f1 n m) (raise_depth_formula f2 n m)
-- | _ (all f) n m := all (raise_depth_formula f n (m+1))

-- def substitute_formula : ∀ {l}, preformula l → (term L) → ℕ → preformula l
-- | _ (true L) s n := true
-- | _ (false L) s n := false
-- | _ (equal t1 t2) s n := equal (substitute_term L t1 s n) (substitute_term L t2 s n)
-- | _ (rel R) s n := rel R
-- | _ (apprel f t) s n := apprel (substitute_formula f s n) (substitute_term t s n)
-- | _ (imp f1 f2) s n := imp (substitute_formula f1 s n) (substitute_formula f2 s n)
-- | _ (all f) s n := all (substitute_formula f s (n+1))


-- def substitute_preformula : Π n : ℕ, Π (ψ : preformula n), term → {x : ℕ // x ∈ (free_vars_preformula _ ψ)} → preformula n
-- | _ (true L) t x := true
-- | _ (false L) t x := false
-- | _ (equal t1 t2) := equal (substitute_preformula _ _ _ _ t1) (substitute_preformula _ _ _ _ t2)

