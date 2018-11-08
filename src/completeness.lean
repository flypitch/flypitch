import .fol order.zorn order.filter logic.basic data.finset data.set tactic.tidy .completion

local attribute [instance, priority 0] classical.prop_decidable

open fol

lemma easy_direction_completeness (L : Language)
(T : Theory L) : (∃ (M : Structure L), nonempty ↥M ∧ M ⊨ T) → is_consistent T :=
begin
  intros H1 H2, cases H1 with M hM, cases hM with h_nonempty hM,
  have inconsis : M ⊨ (⊥ : sentence L),
    fapply soundness,
    repeat{assumption}
end

lemma hard_direction_completeness (L : Language) (T : Theory L) : is_consistent T → (∃ (M : Structure L), nonempty ↥M ∧ M ⊨ T) :=
sorry

/- Note: in the not-easy direction, the term model of a complete Henkin theory will contain a constant witnessing "∃ x, x = x" or something like that, and so will not be empty. -/
theorem completeness {L : Language} (T : Theory L) : is_consistent T ↔ (∃ M : Structure L, (nonempty M) ∧ M ⊨ T) :=
begin
  split, swap,
  {apply easy_direction_completeness},
  {apply hard_direction_completeness}
end