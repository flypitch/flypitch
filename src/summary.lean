/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
import .zfc' .completeness .print_formula .bfol

open fol bSet pSet lattice collapse_algebra

/-
This file summarizes:
 - important definitions with #print statements, and
 - important theorems with duplicated proofs

 The user is encouraged to use their editor's jump-to-definition
 feature to inspect the source code of any expressions which are
 printed or which occur in the proofs below.
-/

#print Language

#print preterm

#print preformula

#print term

#print formula

#print sentence

#print soundness

#print prf

#print provable

#print is_consistent

#print pSet

#print bSet

#print L_ZFC'

#print ZFC'

#eval print_formula_list ([axiom_of_emptyset, axiom_of_pairing, axiom_of_extensionality, axiom_of_union, axiom_of_powerset, axiom_of_infinity, axiom_of_regularity, zorns_lemma])

#print CH_f

#print 𝔹_cohen

#print 𝔹_collapse

#check completeness

theorem godel_completeness_theorem {L} (T) (ψ : sentence L) : T ⊢' ψ ↔ T ⊨ ψ :=
begin
  refine ⟨λ _, satisfied_of_provable _ _ ‹_›, _⟩,
  classical, by_contra H, push_neg at H,
  rcases nonempty_model_of_consis (consis_not_of_not_provable H.right) with ⟨⟨M,HM⟩, H_nonempty⟩,
  refine absurd H.left (not_satisfied_of_model_not _ _ _), swap,
  exact ((by simp at HM; simp*) : (⟨M, by tidy⟩ : Model T) ⊨ _), from ‹_›
end

#check boolean_soundness

theorem boolean_valued_soundness_theorem {L} {β} [complete_boolean_algebra β] {T : Theory L}
  {A : sentence L} (H : T ⊢ A) : T ⊨[β] A :=
forced_of_bsatisfied $ boolean_formula_soundness H

theorem fundamental_theorem_of_forcing {β} [nontrivial_complete_boolean_algebra β] :
  ⊤ ⊩[V β] ZFC' :=
begin
  change ⊤ ≤ _, bv_intro f, bv_intro H,
  repeat{auto_cases}; try{subst H}; try {cases H},
  from bSet_models_Zorn _,
  from bSet_models_regularity _,
  from bSet_models_infinity _,
  from bSet_models_powerset _,
  from bSet_models_union _,
  from bSet_models_extensionality _,
  from bSet_models_pairing _,
  from bSet_models_emptyset _,
  from bSet_models_collection _ ‹_›
end

theorem ZFC'_is_consistent {β : Type} [nontrivial_complete_boolean_algebra β] :
  is_consistent ZFC' := consis_of_exists_bmodel (bSet_models_ZFC' β)

def CH_sentence := CH_f

theorem CH_unprovable_from_ZFC : ¬ (ZFC' ⊢' CH_sentence) :=
unprovable_of_model_neg _ (fundamental_theorem_of_forcing) (nontrivial.bot_lt_top) neg_CH_f

theorem neg_CH_unprovable_from_ZFC : ¬ (ZFC' ⊢' ∼CH_sentence) :=
unprovable_of_model_neg (V 𝔹_collapse) (bSet_models_ZFC' _)
  (nontrivial.bot_lt_top) (by {rw forced_in_not, from V_𝔹_collapse_models_CH})

def independent {L : Language} (T : Theory L) (f : sentence L) : Prop :=
¬ (T ⊢' f ∨ T ⊢' ∼f)

theorem independence_of_CH : independent ZFC' CH_f :=
begin
  have := CH_unprovable_from_ZFC,
  have := neg_CH_unprovable_from_ZFC,
  finish
end

#print axioms CH_unprovable_from_ZFC
/- `propext` (propositional extensionality), `classical.choice` (a type-theoretic choice principle) and `quot.sound` (quotients) are the standard axioms in Lean. -/

#print axioms neg_CH_unprovable_from_ZFC
/- same as above, plus axiomatization of ℵ₁ -/

#print axioms independence_of_CH
/- same as above, plus axiomatization of ℵ₁ -/
