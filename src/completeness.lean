import .fol order.zorn order.filter logic.basic data.finset data.set tactic.tidy .completion

local attribute [instance, priority 0] classical.prop_decidable

open fol

lemma false_of_nonempty_model_of_inconsis {L : Language} {T: Theory L} (P_inconsis : T ⊢ (⊥ : sentence L)) (M : Structure L) (hM : M ⊨ T) (h_empty : ¬ nonempty M) : false :=
begin
have P_exists : sprf T begin split, swap, exact ∃' (&0 ≃ &0), repeat{constructor} end,
apply exfalso, apply P_inconsis,

end

lemma easy_direction_completeness (L : Language) (T : Theory L) : (∃ (M : Structure L), M ⊨ T) → is_consistent T :=
begin
  intro H,
  have witness := @instantiate_existential (Structure L) (λ M, M ⊨ T) H begin fapply nonempty_of_exists, exact λ M, M ⊨ T, exact H end,
  cases witness with M hM,
  unfold all_ssatisfied_in at hM,
  by_contra, rename a h_contra,
  unfold is_consistent at h_contra,
  have proof_of_false : T ⊢ (⊥ : sentence L),
    exact dne4 h_contra,

  have inconsis_model : M ⊨ (⊥ : sentence L),
    {fapply soundness, exact T, assumption, swap, exact hM,
      by_cases nonempty M, assumption, -- why do we need nonempty M to apply soundness?
         sorry -- yikes
        },
  
  unfold ssatisfied_in realize_formula_below at inconsis_model,
  tidy,
end


theorem completeness {L : Language} (T : Theory L) : is_consistent T ↔ (∃ M : Structure L, M ⊨ T) :=
begin
  split, swap,
  {apply easy_direction_completeness},
  {sorry}
end
