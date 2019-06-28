/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
import .henkin

local attribute [instance, priority 0] classical.prop_decidable

open fol fol.Lhom

lemma satisfied_of_provable {L : Language} (T : Theory L) (ψ : sentence L) : T ⊢' ψ → T ⊨ ψ :=
λ _, soundness $ classical.choice ‹_›

lemma completeness_for_inconsistent_theories {L : Language} (T : Theory L) (ψ : sentence L) (h_inconsis : ¬ is_consistent T) : T ⊢' ψ ↔ T ⊨ ψ :=
⟨satisfied_of_provable _ _, λ _, exfalso' $ classical.by_contradiction ‹_›⟩ 

/- T is consistent iff there is a nonempty model of T -/
theorem model_existence {L : Language} (T : Theory L) : is_consistent T ↔ (∃ M : Structure L, (nonempty M) ∧ M ⊨ T) :=
begin
  refine ⟨_,_⟩; intro H,
    { refine ⟨reduct (@henkin_language_over L T H)
        (term_model $ completion_of_henkinization H), ⟨_,_⟩⟩,
      { exact reduct_nonempty_of_nonempty (by simp[fol.nonempty_term_model]) },
      { exact reduct_of_complete_henkinization_models_T _ } },
    { rcases H with ⟨M, ⟨H_nonempty, H_sat⟩⟩,
      exact λ _, false_of_satisfied_false (satisfied_of_provable _ _ ‹_› ‹_› ‹_›) }
end

noncomputable def nonempty_model_of_consis {L : Language} {T : Theory L} (hT : is_consistent T) : Σ' M : Model T, nonempty M.fst.carrier :=
begin
  have := (model_existence T).mp hT, apply classical.psigma_of_exists,
  rcases this with ⟨M, hM, h_satisfied⟩,
  apply exists.intro, swap, exact ⟨M, h_satisfied⟩, exact hM
end

/-- model_existence is implied by completeness --/
theorem model_existence_of_completeness {L : Language} (T : Theory L) (h_completeness : ∀ (T : Theory L) (ψ : sentence L), T ⊢' ψ ↔ T ⊨ ψ) : is_consistent T ↔ (∃ M : Structure L, (nonempty M) ∧ M ⊨ T) :=
begin
  refine ⟨_,_⟩; intro H,
    { by_contra H', push_neg at H', apply H, finish },
    { intro H', rcases H with ⟨_,_,_⟩, rw[h_completeness] at H',
      exact false_of_satisfied_false (H' ‹_› ‹_›) }
end

theorem completeness {L : Language} (T : Theory L) (ψ : sentence L) : T ⊢' ψ ↔ T ⊨ ψ :=
begin
  refine ⟨λ _, satisfied_of_provable _ _ ‹_›, _⟩, by_contra H, push_neg at H,
  rcases nonempty_model_of_consis (consis_not_of_not_provable H.right) with ⟨⟨M,HM⟩, H_nonempty⟩,
  refine absurd H.left (not_satisfied_of_model_not _ _ _), swap,
  exact ((by simp at HM; simp*) : (⟨M, by tidy⟩ : Model T) ⊨ _), from ‹_›
end

theorem compactness {L : Language} {T : Theory L} {f : sentence L} : 
  T ⊨ f ↔ ∃ fs : finset (sentence L), (↑fs : Theory L) ⊨ (f : sentence L) ∧ ↑fs ⊆ T :=
begin
  rw [<-(completeness T f), theory_proof_compactness_iff], simp only [completeness]
end
