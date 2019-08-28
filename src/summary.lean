/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
import .zfc' .completeness .print_formula .forcing_CH_old

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

#print boolean_soundness

#print completeness

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

theorem godel_completeness_theorem {L} (T) (ψ : sentence L) : T ⊢' ψ ↔ T ⊨ ψ :=
begin
  suffices : T ⊨ ψ → T ⊢' ψ, by exact ⟨(by apply satisfied_of_provable), this⟩,
  intro hψ, haveI : decidable (T ⊢' ψ) := classical.prop_decidable _, by_contra,
  suffices : ¬ T ⊨ ψ, by contradiction,
  have := nonempty_model_of_consis (consis_not_of_not_provable a),
  rcases this with ⟨⟨M,hM⟩, nonempty_M⟩;
  fapply not_satisfied_of_model_not,
  refine ⟨M,_⟩,
  intros f hf, apply hM, simp[hf],
  unfold Model_ssatisfied, dsimp, apply hM _,
  simpa only [set.mem_insert_iff, true_or, eq_self_iff_true, set.union_singleton]
end

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

theorem CH_unprovable_from_ZFC : ¬ (ZFC' ⊢' CH_sentence) := sorry
-- begin
--   intro H,
--   suffices forces_false : ⊤ ⊩[V 𝔹] bd_falsum,
--     from absurd (nontrivial.bot_lt_top) (not_lt_of_le forces_false),
--   refine forced_absurd _ _, exact ZFC', exact CH_f, swap, apply neg_CH_f,
--   let prf_of_CH_f := sprovable_of_provable (classical.choice H),
--   have CH_f_true := boolean_soundness prf_of_CH_f (V_𝔹_nonempty),
--   convert CH_f_true, rw[inf_axioms_top_of_models (bSet_models_ZFC' _)]
-- end

#print axioms CH_unprovable_from_ZFC
/- `propext` (propositional extensionality), `classical.choice` (a type-theoretic choice principle) and `quot.sound` (quotients) are the standard axioms in Lean. -/
