/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
import .henkin

local attribute [instance, priority 0] classical.prop_decidable

open fol fol.Lhom

lemma completeness_for_inconsistent_theories {L : Language} (T : Theory L) (ψ : sentence L) (h_inconsis : ¬ is_consistent T) : T ⊢' ψ ↔ T ⊨ ψ :=
 ⟨by {intro H, fapply soundness, exact classical.choice H}, (by {intro H, exact exfalso' (classical.by_contradiction h_inconsis)})⟩

lemma satisfied_of_provable {L : Language} (T : Theory L) (ψ : sentence L) : T ⊢' ψ → T ⊨ ψ :=
by {intro H, exact soundness (classical.choice H)}

/- T is consistent iff there is a nonempty model of T -/
theorem model_existence {L : Language} (T : Theory L) : is_consistent T ↔ (∃ M : Structure L, (nonempty M) ∧ M ⊨ T) :=
begin
split, swap,
  {intro H, rcases H with ⟨M,⟨h_nonempty, hM⟩⟩, intro,
   apply false_of_satisfied_false, repeat{assumption},
   apply satisfied_of_provable T ⊥ a, repeat{assumption}},
  {intro hT, refine ⟨_,_⟩,
   apply reduct, exact @henkin_language_over L T hT,
   apply term_model, exact completion_of_henkinization hT,
   refine ⟨_,_,⟩, fapply Lhom.reduct_nonempty_of_nonempty, simp[fol.nonempty_term_model],
   apply reduct_of_complete_henkinization_models_T}
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
  split, swap,
  {intros H1 H2, cases H1 with M hM, cases hM with h_nonempty hM,
  have inconsis : M ⊨ (⊥ : sentence L),
    fapply soundness,
    repeat{assumption},
    exact classical.choice H2},

  {by_contra, simp only [*, -a, not_exists, not_imp, not_and, nonempty.forall] at a, cases a,
  have  : ¬ T ⊢' (⊥ : sentence L) → ¬ T ⊨ (⊥ : sentence L), 
  by simp only [@h_completeness T ⊥, imp_self], have H := this a_left, unfold ssatisfied at H,
  simp only [*, -H, fol.realize_sentence_false, nonempty.forall] at H,
  fapply absurd, exact ∀ ⦃S : Structure L⦄, S.carrier → S ⊨ T → false, repeat{assumption}}
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
