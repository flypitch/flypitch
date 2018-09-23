import .language_term_n_de_bruijn
import data.vector
open term
open formula
universe u



def prod_n : ∀ (α : Type) (n: nat), Type
    | α 0 := α 
    | α (n+1) := α × prod_n α n


def n_ary_prop  := λ α n, (vector α n) → Prop
def n_ary_fn := λ α n, (vector α n) → α


structure L_Structure {L : Language} :=
    struct :: (A: Type) 
              (const_map : L.consts → A) 
              (rel_map : ∀ n, L.relations n → n_ary_prop A n) 
              (fun_map : ∀ n, L.functions n → n_ary_fn A n)

def realiztion : ∀