/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
import .fol .zfc' .completeness

local attribute [instance, priority 0] classical.prop_decidable

open fol lattice

section independence

/- ¬ (T ⊢' f) is implied by ∃ M : Model T, M ⊢ ∼ f -/
lemma unprovable_of_model_negation {L : Language} {T : Theory L} {hT : is_consistent T} {f : sentence L} (S : Structure L) (hS : S ⊨ T) {h_nonempty : nonempty S} (hS' : S ⊨ ∼f) : ¬ (T ⊢' f) :=
begin
  revert hS', by_contra, have H : ¬S ⊨ f ∧ T ⊢' f, by {simp at a, exact a},
  suffices : S ⊨ f, by {apply false_of_Model_absurd ⟨S, hS⟩ this (by exact H.left)},
  apply (completeness T f).mp H.right, repeat{assumption}
end

lemma independence_of_exhibit_models {L : Language} {T : Theory L} {hT : is_consistent T} {f : sentence L} (M1 : Model T) (H1 : M1 ⊨ f) (M2 : Model T) (H2 : M2 ⊨ ∼f) {h_nonempty1 : nonempty M1.fst} {h_nonempty2 : nonempty M2.fst} : ((¬ T ⊢' f) ∧ (¬ T ⊢' ∼f)) :=
by exact ⟨by {apply unprovable_of_model_negation, exact hT, exact M2.snd, repeat{assumption}},
         by {apply unprovable_of_model_negation, exact hT, exact M1.snd, assumption, simpa}⟩

--TODO(everyone)
theorem CH_consistent {β} [nontrivial_complete_boolean_algebra β] : ∃ M : bModel β ZFC', (nonempty M.fst) ∧ ⊤ ⊩[M.1] CH_f := sorry

--TODO(jesse)
theorem neg_CH_consistent {β} [nontrivial_complete_boolean_algebra β] : ∃ M : bModel β ZFC', (nonempty M.fst) ∧ ⊤ ⊩[M.1] ∼ CH_f := sorry

-- theorem independence_of_CH : (¬ ZFC' ⊢' CH_f) ∧ (¬ ZFC' ⊢' ∼ CH_f) :=
-- begin
--   have := CH_consistent, have := neg_CH_consistent, repeat{auto_cases},
--   apply @independence_of_exhibit_models L_ZFC' ZFC' ZFC'_consistent CH_f,
--   show Model ZFC', exact this_w_1, show Model ZFC', exact this_w, repeat{assumption}
-- end
  

end independence
