
/- This definition of the "term" datatype is mutually inductive, along with a "term_vec" datatype. 
  It would be more elegant and probably easier to use one inductive type Lean library's "vector" datatype, 
  but it doesn't work out of the box due to (vector α n) taking the type α as an argument:

        inductive term' : Type
            | var : ℕ → Type
            | apply : ∀ f : L.functions, vector term' (L.arityF f) → term'
  
  If we use this definition, there is an error message saying the nested occurrence of the type "contains variables that are not parameters."
 
  The implementation here also has problems: Lean cannot figure out how to prove that induction over the  mutually inductive types term/term_vec is well-founded.
  One of Lean's basic strategies to accomplish this is the has_sizeof typeclass; has_sizeof.sizeof is, ideally, a function from a Type to ℕ which decreases w.r.t. complexity;
  For example sizeof (term.apply f t_vec) should be greater than sizeof t_vec; and in turn sizeof t_vec should be greater than that of its members.
  The two functions sizeof_vec and sizeof_term_vec are meant to accomplish this, but it hasn't been done quite right; 
  I think the problem might have to do with the use of "sizeof" within the two functions: because the  function sizeof_term is passed an instance of has_sizeof  term,
  this means that the and means that the outermost "sizeof term" is slightly, and invisibly, different than the innermost "sizeof term". Typeclasses are a mystery to me.
  Whatever the problem, it leads to this cryptic error , which you can see below on the first use of free_vars_vec:
    
    nested exception message:
        failed
        state:
        L : Language,
        f : L.functions,
        l : term_vec L (L.arityF f),
        this : 1 + (L.arityF f + sizeof_term_vec L (L.arityF f) l) < sizeof_term L (term.apply f l)
        ⊢ 1 + (L.arityF f + sizeof_term_vec L (L.arityF f) l) < sizeof_term L (term.apply f l)

    There must be a slight difference between the type of "this" and the conclusion Lean wishes to reach, or it could be discharged immediately.
 -/
import data.vector

structure Language := 
    language :: (relations : Type) (functions : Type ) (arityF :  functions →  nat) (arityR : relations → nat)
variable L : Language



universe u
mutual inductive  term, term_vec
with term : Type
    | var : nat → term
    | apply: ∀ (f : L.functions ), (term_vec (L.arityF f)) → term
with term_vec : Π (n : nat), Type
    | nil : term_vec 0
    | cons : Π {n: nat}, term → term_vec n → term_vec (n+1)

def term_vec.length {n : nat} : term_vec L n → ℕ := λ t, n

def in_term_vec : Π n, term L → term_vec L n → Prop
    | 0 t (term_vec.nil L) := false
    | (m + 1) t (term_vec.cons t' ts) := t = t' ∨ in_term_vec m t ts

def rel_term : term L → term L → Prop 
    | (term.var _ n) (term.var _ m) := false
    |  t (term.apply f ts) := (in_term_vec L (term_vec.length L ts) t ts ) ∨  (∃ t', (in_term_vec L (term_vec.length L ts) t' ts ∧ rel_term t t')) 

 def  sizeof_term_vec [β : has_sizeof (term L)] : Π n, term_vec L n  → nat
    | 0 (term_vec.nil L) := 0
    | _ (term_vec.cons (term.var _ _ ) ts) := 1 + sizeof ts
    | _ (term_vec.cons (term.apply f ts') ts) := sizeof ts' + sizeof ts

instance term_vec_has_sizeof {n : nat} : has_sizeof (term_vec L n) := ⟨ sizeof_term_vec L n ⟩ 

def sizeof_term [β : has_sizeof (Π n, (term_vec L n))] : term L → ℕ 
    | (term.var _ _ ) := 0
    | (term.apply f ts) := 2 + (L.arityF f) + sizeof ts

instance term_has_sizeof : has_sizeof (term L) := ⟨ sizeof_term L ⟩ 

mutual def free_vars, free_vars_vec 
with free_vars : (term L) → list nat 
    | (term.var L n) := [n]
    | (term.apply f l) :=  have 1 + (L.arityF f + sizeof_term_vec L (L.arityF f) l) < sizeof_term L (term.apply f l), by
    {simp [sizeof_term, sizeof, has_sizeof.sizeof, add_lt_add_left ], admit},
    free_vars_vec (L.arityF f) l
with free_vars_vec : Π n, (term_vec L n) → list nat
    | 0 (term_vec.nil L) := []
    | _ (term_vec.cons t ts) := nat_list_union (free_vars t) (free_vars_vec ts)

definition substitute_formula : list nat → list (term L) → formula L := sorry