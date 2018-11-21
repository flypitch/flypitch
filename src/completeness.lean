import .fol order.zorn order.filter logic.basic data.finset data.set tactic.tidy .henkin .language_extension

local attribute [instance, priority 0] classical.prop_decidable

open fol

def double_negation_elim {L} {T : Theory L} {f : sentence L} : T ⊢ (f ⟹ (⊥ : sentence L)) ⟹ (⊥ : sentence L) → T ⊢ f :=
begin
  intro, fapply falsumE, fapply impE, exact f.fst, all_goals{unfold fol.not},
  fapply deduction, 
  fapply impI, fapply axm1, fapply exfalso, fapply deduction, assumption
end

lemma consis_not_of_not_provable {L} {T : Theory L} {f : sentence L} {hT : is_consistent T} : ¬ T ⊢' f → is_consistent (T ∪ {∼f}) :=
begin
  intro, by_contra, have := classical.choice (classical.by_contradiction a_1),
  simp only [*, set.union_singleton, fol.bounded_preformula.fst] at this,
  have : Theory.fst T ⊢ f.fst, fapply double_negation_elim, fapply impI,
  unfold Theory.fst at this, rw[set.image_insert_eq] at this, exact this,
  have := nonempty.intro this, contradiction
end

theorem completeness {L : Language} (T : Theory L) (ψ : sentence L) : T ⊢' ψ ↔ T ⊨ ψ :=
begin
  split,
  {intro H, fapply soundness, exact classical.choice H},
  {by_cases is_consistent T, swap,
            {intro, fapply nonempty.intro, fapply exfalso, fapply classical.choice,
            unfold is_consistent at h, have : T ⊢' (⊥ : sentence L),
            fapply classical.by_contradiction, exact h, exact this},
    {by_contra, simp[*, -a] at a, cases a with H2 H1, 
    
    have hT : is_consistent (T ∪ {∼ψ}), by {fapply consis_not_of_not_provable, repeat{assumption}},
    have T' := (complete_henkinization hT), cases T' with L' T', cases T' with T'1 T'2,
    cases T'1 with T'' HT'', cases T'2 with T''_henkin T''_complete,
    have : ¬ T ⊨ ψ,
    {unfold ssatisfied, rw[not_forall], fapply exists.intro, fapply Lhom.reduct,
    exact L'.fst, exact L'.snd, fapply term_model, exact T'', intro H,
    /- The term model is nonempty -/
    have h_nonempty :  nonempty ↥(Lhom.reduct (L'.snd) (term_model T'')),
      {fapply Lhom.reduct_nonempty_of_nonempty, exact fol.nonempty_term_model T''_henkin},
    /- The L-reduct of the term model of a complete Henkinization of T is a model of T -/
    have h_all_realized_of_reduct : Lhom.reduct (L'.snd) (term_model T'') ⊨ T,
      {sorry},
    /- Since the term model models T'' and T'' contains ∼ψ, the term model satisfies ∼ψ -/
    have h_not_psi : Lhom.reduct (L'.snd) (term_model T'') ⊨ ∼ψ,
      {have := @term_model_ssatisfied L'.fst T'' T''_complete T''_henkin,
       /- Now we have to take ∼ψ, show that as an L'-sentence it's in T'', but since it was
       an L-sentence to begin with it's satisfied by the L-reduct of the term model-/
       have h_expansion : Lhom.on_sentence L'.snd ∼ψ ∈ T'', by sorry,
       have := this h_expansion,
       sorry},
    have h_psi := H h_nonempty h_all_realized_of_reduct,
    simp only [*, forall_prop_of_true, forall_prop_of_false, not_true,
              fol.realize_sentence_not, not_false_iff, -h_not_psi] at h_not_psi h_psi,
    exact h_not_psi},
    {contradiction}, 
    },
  } 
end

/- Note: in the not-easy direction, the term model of a complete Henkin theory will contain a constant witnessing "∃ x, x = x" or something like that, and so will not be empty. -/

/-- Corollary of completeness --/
theorem completeness'' {L : Language} (T : Theory L) : is_consistent T ↔ (∃ M : Structure L, (nonempty M) ∧ M ⊨ T) :=
begin
  split, swap,
  {intros H1 H2, cases H1 with M hM, cases hM with h_nonempty hM,
  have inconsis : M ⊨ (⊥ : sentence L),
    fapply soundness,
    repeat{assumption},
    exact classical.choice H2},

  {by_contra, simp only [*, -a, not_exists, not_imp, not_and, nonempty.forall] at a, cases a,
  have  : ¬ T ⊢' (⊥ : sentence L) → ¬ T ⊨ (⊥ : sentence L),
  by simp only [completeness T ⊥, imp_self], have H := this a_left, unfold ssatisfied at H,
  simp only [*, -H, fol.realize_sentence_false, nonempty.forall] at H,
  fapply absurd, exact ∀ ⦃S : Structure L⦄, S.carrier → S ⊨ T → false, repeat{assumption}}
end

theorem compactness {L : Language} {T : Theory L} {f : sentence L} : 
  T ⊨ f ↔ ∃ fs : finset (sentence L), ↑fs ⊨ f ∧ ↑fs ⊆ T :=
begin
  rw [←completeness T f, theory_proof_compactness_iff], simp [completeness]
end
