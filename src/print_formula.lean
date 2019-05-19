/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Andrew Tindall, Jesse Han, Floris van Doorn
-/

import .fol set_theory.zfc .zfc'

open fol ZFC'_rel ZFC'_func

-- ugly but working (str_formula says it's not well-founded recursion, but it evaluates anyways)
meta def str_preterm : ∀ n m : ℕ, ℕ → bounded_preterm L_ZFC' n m → string
 | n m z &k := "x" ++ to_string(z - k)
 | n m z (bd_func emptyset) := "∅"
 | n m z (bd_func pr) := "pair"
 | n m z (bd_func ω) := "ω"
 | n m z (bd_func P) := "𝒫"
 | n m z (bd_func Union) := "⋃"
 | n m z (bd_app t₁ t₂) := (str_preterm _ _ z t₁) ++ "(" ++ (str_preterm _ _ z t₂) ++ ")"

meta def str_term : ∀ n : ℕ, ℕ → bounded_term L_ZFC' n → string
:= λ n, str_preterm n 0
 -- | n m &k := "x" ++ to_string(m - k.val)
 -- | n m (bd_func emptyset) := "∅"
 -- | _ _ (bd_func ω) := "ω"
 -- | n m (bd_app t₁ t₂) := (str_term (n+1) m t₁) ++ (str_term 0 m t₂)

meta def str_preformula : ∀ n m : ℕ, ℕ → bounded_preformula L_ZFC' n m → string
 | _ _ _ (bd_falsum ) := "⊥"
 | n m z (bd_equal a b) := str_preterm n m z a ++ " = " ++ str_preterm n m z b
 | n m z (a ⟹ b) := str_preformula n m z a ++ " ⟹ " ++ str_preformula n m z b
 | n m z (bd_rel _) := "∈"
 | n m z (bd_apprel a b) := str_preformula n (m+1) z a ++ "(" ++ str_term n z b ++ ")"
 | n m z (∀' t) := "(∀x" ++ to_string(z+1) ++ "," ++ str_preformula (n+1) m (z+1) t ++ ")"

meta def str_formula : ∀ {n : ℕ}, bounded_formula L_ZFC' n → ℕ → string
-- := λ n f k, str_preformula n 0 k f
 | n ((f₁ ⟹ (f₂ ⟹ bd_falsum)) ⟹ bd_falsum) m:= "(" ++ str_formula f₁ m ++ "∧" ++ str_formula f₂ m ++ ")"
 | n ((f₁ ⟹ bd_falsum) ⟹ f₂) m := "(" ++ str_formula f₁ m ++ " ∨ " ++ str_formula f₂ m ++ ")"
 | n (bd_equal s1 s2) m := "(" ++ str_term n m s1 ++ " = " ++ str_term n m s2 ++ ")"
 | n (∀' f) m := "(∀x"++ to_string(m + 1) ++ "," ++ (str_formula f (m+1) ) ++ ")"
 | _ bd_falsum _ := "⊥"
| n (f ⟹ bd_falsum) m := "~" ++ str_formula f m
 | n (bd_apprel (bd_apprel (bd_rel ((ε : L_ZFC'.relations 2))) a) b) m := str_preterm _ _ m a ++ " ∈ " ++ str_preterm _ _ m b
 | n (bd_apprel (f₁) f₂) m := str_preformula n 1 m f₁ ++ "(" ++ str_term n m f₂ ++ ")"
 | n (bd_imp a b) m := "(" ++ str_formula a m ++ " ⟹ " ++ str_formula b m ++ ")"

meta def print_formula : ∀ {n : ℕ}, bounded_formula L_ZFC' n → string := λ f, str_formula f ‹_›

@[instance]meta def formula_to_string {n} : has_to_string (bounded_formula L_ZFC' n) := ⟨print_formula⟩

meta def print_formula_list {n} (axms : list (bounded_formula L_ZFC' n)) : tactic unit :=
do tactic.trace (to_string axms)
-- TODO(jesse) format this so that newlines are inserted after commas

section test

/- ∀ x, ∀ y, x = y → ∀ z, z = x → z = y -/
meta def testsentence : sentence L_ZFC' := ∀' ∀' (&1 ≃ &0 ⟹ ∀' (&0 ≃ &2 ⟹ &0 ≃ &1))

-- #eval print_formula testsentence
-- #eval print_formula CH_f
-- #eval print_formula axiom_of_powerset
-- #eval print_formula axiom_of_emptyset
-- #eval print_formula_list ([axiom_of_emptyset, axiom_of_pairing])
end test
