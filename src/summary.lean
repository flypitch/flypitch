/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
import .zfc' .completeness .print_formula

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

#print L_ZFC

#print ZFC

#eval print_formula_list ([axiom_of_emptyset, axiom_of_pairing, axiom_of_extensionality, axiom_of_union, axiom_of_powerset, axiom_of_infinity, axiom_of_regularity, zorns_lemma])

#print CH

#print CH_f

#print 𝔹_cohen

#print 𝔹_collapse

theorem godel_completeness_theorem {L} (T) (ψ : sentence L) : T ⊢' ψ ↔ T ⊨ ψ :=
completeness T ψ

theorem boolean_valued_soundness_theorem {L} {β} [complete_boolean_algebra β] {T : Theory L}
  {A : sentence L} (H : T ⊢ A) : T ⊨[β] A :=
forced_of_bsatisfied $ boolean_formula_soundness H

theorem fundamental_theorem_of_forcing {β} [nontrivial_complete_boolean_algebra β] :
  ⊤ ⊩[V β] ZFC :=
bSet_models_ZFC β

theorem ZFC_is_consistent {β : Type} [nontrivial_complete_boolean_algebra β] :
  is_consistent ZFC :=
consis_of_exists_bmodel (bSet_models_ZFC β)

theorem CH_unprovable : ¬ (ZFC ⊢' CH_f) :=
CH_f_unprovable

theorem neg_CH_unprovable : ¬ (ZFC ⊢' ∼CH_f) :=
neg_CH_f_unprovable

def independent {L : Language} (T : Theory L) (f : sentence L) : Prop :=
¬ T ⊢' f ∧ ¬ T ⊢' ∼f

theorem independence_of_CH : independent ZFC CH_f :=
by finish [independent, CH_unprovable, neg_CH_unprovable]

#print axioms independence_of_CH
/- `propext` (propositional extensionality),
   `classical.choice` (a type-theoretic choice principle), and
   `quot.sound` (quotients) are the standard axioms in Lean. -/
