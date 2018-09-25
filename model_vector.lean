import .language_term_n_de_bruijn
import data.vector
import init.data.nat.lemmas


open term
open formula

universe u
variable L: Language


def prod_n : ∀ (α : Type) (n: nat), Type
    | α 0 := α 
    | α (n+1) := α × prod_n α n


def n_ary_prop  := λ α n, (vector α n) → Prop
def n_ary_fn := λ α n, (vector α n) → α

def map_over_term: ∀ α n, term L (vec n) → (term L atm → α) → vector α n
    | _ 0 (nil L) _ := vector.nil
    | α (n+1) (conj _ t ts) f := vector.cons (f t) (map_over_term α n ts f)


structure L_Structure :=
    struct :: (L : Language)
              (A: Type) 
              (const_map : L.consts → A) 
              (rel_map : ∀ n, L.relations n → n_ary_prop A n) 
              (fun_map : ∀ n, L.functions n → n_ary_fn A n)
variable S: L_Structure


/-  this realization function is a little fast and loose. 
    the idea is basically that the term f(v0, v5) should act as if it has SIX free variables, not two.

    ⟦f(v0,v5)⟧ := λ (x0, x1, x2, x3, x4, x5), ⟦f⟧(x0, x5). 

    the reason for this decision is that this way, we do not need to keep track of what "depth" our term is at in order to find the realization. 
    (keeping track of depth was going to be a major problem in this vector-based implementation, and i suspect in any other where we use de bruijn indices)

    of course, this means that realization does not respect alpha-equivalence...
    However, one of the perks of of de bruijn indices is that you don't have to worry about α-equivalence! 
    
    also I can't get lean to see that vector α j is the same type as vector α (min j (max j k)), but this is hopefully an easy fix.
    -/

/- added a partially-proven lemma for the bit at the end
   looks like to finish this we need a lemma which says
   max(j, k) = j => max(j+1, k) = max(j+1, max(j,k))
   then we should be able to just hit with simp


   I also dislike the whole "include ALL the variables!" thing, but...
   since we have function extensionality it should be """fine""".
   --- Jesse
 -/

lemma min_max_lemma (j k : ℕ) : min j (max j k) = j :=
begin
induction j with j ih,
  {induction k with k ih,
  {simp [le_refl]},
        {simp [le_refl, zero_lt_one]}},
  {induction k with k ih,
  admit}
end

mutual def realization_atm, realization_vec
with realization_atm : ∀ (t: term S.L atm), (Σ n, (vector S.A n → S.A))
    | (const c) := ⟨ 0, λ v, S.const_map c⟩ 
    | (var _ n) := let pf: n < n+1 :=  begin apply lt_add_of_pos_right, apply zero_lt_one end in
         ⟨ n+1,  λ v: vector S.A (n+1), (v.nth {val := n, is_lt := pf}) ⟩ 
    | (apply n f ts) := have 1 + (n + term_sizeof (S.L) (vec n) ts) < term_sizeof (S.L) atm (apply n f ts), from 
        begin
            simp [term_sizeof],
            apply add_lt_add_left,
            apply add_lt_add_right,
            apply nat.succ_lt_succ,
            apply nat.zero_lt_succ
        end,
    match realization_vec n ts with 
        | ⟨m, g⟩ := ⟨m, (S.fun_map n f) ∘ g⟩ end
with realization_vec: ∀ m (t: term S.L (vec m)), (Σ n, (vector S.A n → vector S.A m))
    | 0 (nil L) := ⟨0, λ v, vector.nil⟩
    | (n+1) (conj x t ts) := have term_sizeof (S.L) atm t < x + (2 + term_sizeof (S.L) (sum.inr (x + 1)) (conj x t ts)), from 
        begin
            apply lt_add,
            simp [term_sizeof],
            apply lt_add,
            apply nat.lt_add_of_pos_right,
            apply add_lt,
            apply nat.zero_lt_succ
        end,
    match realization_atm t with
        | ⟨j, f⟩ := have 1 + term_sizeof (S.L) (vec x) ts < 2 + term_sizeof (S.L) (sum.inr (x + 1)) (conj x t ts), from
            begin
                simp [term_sizeof],
                apply nat.add_lt_add_left,
                apply lt_add,
                apply nat.lt_add_of_pos_left,
                apply nat.zero_lt_succ
            end,
        match realization_vec n ts with 
            | ⟨k, g⟩ := ⟨ max j k, λv, vector.cons (f (vector.take j v)) (g (vector.take k v)) ⟩ end end 
