
/- Along with the half-finished definition of substitution here is an attempt to define terms using lists instead of vectors.
    The problem is, since the type "list" does ot say anything about the size of the list, it is possible to use this definition to define terms that apply a function of any arity to a list of any length.
    To prevent this from happening, we might be able to use an auxiliary well_formed_term definition, and prove that it is preserved after operations like substitution.
    However, the same well-founded recursion problem reared its head at a certain point -- here it was after writing a really long theorem about the preservation of well-formed-ness.
    If you wait for it to compile, you can read the error message below on
    
        mutual theorem sub_term_well_formed, sub_term_list_well_formed 
    
    It was too much to think about creating a well-founded relation over these theorems; it takes about two minutes just for Lean to read through the tactics as it is.. 
    I'm pretty sure that this approach is not any easier. -/

structure Language := 
    language :: (relations : Type) (functions : Type ) (arityF :  functions →  nat) (arityR : relations → nat)
variable L : Language
variable n : nat

universe u
inductive term 
    | var : nat → term
    | apply: L.functions → list term → term

mutual def well_formed_term, well_formed_term_list 
with well_formed_term : term L -> Prop
    | (term.var L _) := true
    | (term.apply f l) := ((L.arityF f) = list.length l) ∧ (well_formed_term_list l)
with well_formed_term_list : list (term L) → Prop
    | [] := true
    | (list.cons t ts) := (well_formed_term t) ∧ well_formed_term_list ts
def nat_list_union : list nat → list nat → list nat 
    | [] l := l
    | (list.cons n ns) l := if  n ∈ l then list.cons n (nat_list_union ns l) else nat_list_union ns l

def nat_list_remove : nat → list nat → list nat
    | _ [] := []
    | n (list.cons m ms) := if (n=m) then nat_list_remove n ms else list.cons n (nat_list_remove n ms)
def nat_list_max : list nat → nat
    | [] := 0
    | (list.cons n ns) := if n ≥ nat_list_max ns then n else nat_list_max ns
lemma nat_list_max_is_max : ∀ (l : list nat) (n : nat), n ∈ l → (nat_list_max l) ≥ n :=
 begin
    intros l n n_in_l,
    induction l,
        apply absurd,
        apply list.not_mem_nil,
        exact n_in_l,
        exact not_false,
    simp [nat_list_max],
    have ex_mid : (l_hd ≥ nat_list_max l_tl) ∨ ¬ (l_hd ≥ nat_list_max l_tl), by apply decidable.em,
    cases ex_mid,
        have n_or : (n = l_hd ∨ n ∈ l_tl), by {apply list.eq_or_mem_of_mem_cons, exact n_in_l},
        rewrite if_pos,
        cases n_or,
            apply le_of_eq,
            exact n_or,
            apply le_trans,
            apply l_ih,
            exact n_or,
        exact ex_mid,
        exact ex_mid,
        rewrite if_neg,
        have n_or : (n = l_hd ∨ n ∈ l_tl), by {apply list.eq_or_mem_of_mem_cons, exact n_in_l},
        cases n_or,
            apply le_trans,
            have hd_lt : l_hd < nat_list_max l_tl, by {apply iff.mpr, apply lt_iff_not_ge,exact ex_mid},
            apply le_of_lt,
            simp [n_or],
            exact hd_lt,
        apply le_of_eq,
        apply eq.refl,
        apply l_ih,
        exact n_or,
    exact ex_mid
 end
def new_nat_list : list nat → nat := λ l, nat_list_max l + 1
lemma new_is_new : ∀ (l : list nat), ¬ (new_nat_list l ∈ l) :=
begin
    simp [new_nat_list],
    intros l new_in,
    apply absurd,
    apply nat.lt_succ_self, exact nat_list_max l,
    apply not_lt_of_ge,
    apply nat_list_max_is_max,
    simp [nat.succ_eq_add_one],
    exact new_in
end

mutual def free_vars, free_vars_list 
with free_vars : (term L) → list nat 
    | (term.var L n) := [n]
    | (term.apply f l) := free_vars_list l
with free_vars_list : list (term L) → list nat
    | [] := []
    | (list.cons t ts) := nat_list_union (free_vars t) (free_vars_list ts)
inductive formula : Type 
    | equal : term L → term L → formula
    | atomic : ∀ r : L.relations, list (term L) → formula
    | imp : formula → formula → formula
    | not :  formula → formula
    | forallF : nat → formula → formula
open formula 
def choice: list nat → nat := λ l, 1 + nat_list_max l

def sub_list :Type := list (nat × term L)
def in_sub_list : nat → sub_list L → Prop
    | n [] := false
    | n ((m, _) :: s_tl) := (n=m) ∨ (in_sub_list n s_tl)
def find_term_in_sub_list : nat → sub_list L →  term L
    | n [] := term.var L n
    | n ((m, t) :: sl_tl) := if n =m then t else find_term_in_sub_list n sl_tl

def well_formed_sub_list : sub_list L → Prop
    | [] := true
    | ((m, t) :: l_tl) := (¬ in_sub_list L m l_tl) ∧ well_formed_term L t ∧ well_formed_sub_list l_tl
theorem eq_or_mem_of_mem_cons {n m: nat} {l : sub_list L} {t : term L}: (in_sub_list L n ((m, t) :: l)) → n = m ∨ (in_sub_list L n l) :=
assume h, h

mutual def substitute_term, substitute_term_list
with substitute_term : sub_list L → term L → term L
   | sl (term.var L n) := find_term_in_sub_list L n sl
   | sl (term.apply f ts) := term.apply f (substitute_term_list sl ts)
with substitute_term_list : sub_list L → list (term L ) → list (term L)
    | sl [] := []
    | sl (t :: ts) := (substitute_term sl t) :: (substitute_term_list sl ts)
lemma sub_term_list_preserves_length {sl : sub_list L} {ts : list (term L)} : list.length ts = list.length (substitute_term_list L sl ts) :=
begin
induction ts,
simp [list.length, substitute_term_list],
simp [list.length_cons, substitute_term_list, ts_ih]
end

lemma rw_well_formed_term_definition : Π {f : L.functions} {ts : list (term L)}, well_formed_term L (term.apply f ts) → L.arityF f = list.length ts ∧ well_formed_term_list L ts := by {simp [well_formed_term], intros f ts, apply id} 
lemma rw_well_formed_term_list_definition : Π {t ts}, well_formed_term_list L (t :: ts) → well_formed_term L t ∧ (well_formed_term_list L ts) := by {simp [well_formed_term_list], intros t ts wftl,exact wftl}
lemma rw_well_formed_sub_list_definition : Π {hd_fst hd_snd tl}, well_formed_sub_list L ((hd_fst, hd_snd) :: tl) → well_formed_term L hd_snd ∧ well_formed_sub_list L tl  := by {simp [well_formed_sub_list], intros fst snd tl wfsl, apply and.elim_right, exact wfsl}
lemma find_term_well_formed : Π {n : nat} {sl : sub_list L}, well_formed_sub_list L sl → well_formed_term L (find_term_in_sub_list L n sl) := begin
    intros n sl wfsl,
    induction sl,
    simp [find_term_in_sub_list, well_formed_term],
    cases sl_hd,
    simp [find_term_in_sub_list],
        have ex_mid : n = sl_hd_fst ∨ ¬ n = sl_hd_fst, by {apply decidable.em},
        cases ex_mid,
        simp [if_pos ex_mid],
        apply and.elim_left,
        apply rw_well_formed_sub_list_definition,
        exact wfsl,
        simp [if_neg ex_mid],
        apply sl_ih,
        apply and.elim_right,
        apply rw_well_formed_sub_list_definition,
        exact wfsl
end
mutual theorem sub_term_well_formed, sub_term_list_well_formed
with sub_term_well_formed : Π {t: term L} {sl : sub_list L},  well_formed_term L t →  well_formed_sub_list L sl → well_formed_term L (substitute_term L sl t)
    | t sl wft wfsl := 
        begin

            induction t,
                simp [substitute_term],
                induction sl,
                simp [find_term_in_sub_list, well_formed_term],
                cases sl_hd,
                    simp [find_term_in_sub_list],
                    have ex_mid : t = sl_hd_fst ∨ ¬ t = sl_hd_fst, by apply decidable.em,
                    cases ex_mid,
                        simp [if_pos ex_mid],
                        apply and.elim_left,
                        apply and.elim_right,
                        exact wfsl,
                        simp [if_neg ex_mid],
                        have wf_sl : well_formed_sub_list L sl_tl, by {apply and.elim_right, apply and.elim_right, apply wfsl},
                        apply sl_ih,
                        exact wf_sl,
            simp [substitute_term,well_formed_term],
            apply and.intro,
            apply eq.trans,
            apply and.elim_left,
            apply rw_well_formed_term_definition,
            exact wft,
        apply sub_term_list_preserves_length,
        apply sub_term_list_well_formed,
        apply and.elim_right,
        apply rw_well_formed_term_definition,
        exact wft,
        exact wfsl
end
with sub_term_list_well_formed : Π {ts : list (term L)} {sl : sub_list L}, well_formed_term_list L ts → well_formed_sub_list L sl → (well_formed_term_list L (substitute_term_list L sl ts))
    | ts sl wftl wfsl := begin
    repeat {simp [substitute_term_list]},
    induction ts, 
        simp [substitute_term_list, substitute_term_list, substitute_term_list],
        simp [substitute_term_list, well_formed_term_list],
        apply and.intro,
            apply sub_term_well_formed,
            apply and.elim_left,
            apply rw_well_formed_term_list_definition,
            exact wftl,
            exact wfsl,
        apply ts_ih,
        apply and.elim_right,
        apply rw_well_formed_term_list_definition,
        exact wftl,
end

definition substitute_formula : list nat → list (term L) → formula L := sorry