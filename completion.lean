/- Show that every theory can be extended to a complete theory -/

import .language_term_n2 order.zorn order.filter logic.basic
attribute [instance, priority 0] classical.prop_decidable
open fol

section
parameter L : Language
/- complete_Theory L is the subtype of all theories which are complete  -/
def complete_Theory {L : Language} : Type := {T : @Theory L // is_complete T}

lemma dne {p : Prop} (H : ¬¬p) : p := --- from TPIL, is this elsewhere?
                  or.elim (classical.em p)
                  (assume Hp : p, Hp)
                  (assume Hnp : ¬p, absurd Hnp H)


@[reducible] lemma dne2 {p : Prop} : p = ¬ ¬ p :=
begin
refine propext _,
split,
{intro,
{exact (λ (h : ¬ p), absurd a h)}},
{intro a, exact dne a}
end

lemma dne3 {p q : Prop} (h : ¬ p) : (p ∨ q) = q :=
begin
refine propext _,
split,
swap,
intro,
exact or.inr a,
intro,
refine or.elim a _ _,
intro, refine absurd h _,
exact absurd a_1 h,
exact id
end

lemma can_extend {L : Language} (T : @Theory L) (ψ : @sentence L) (h : is_consistent T): (is_consistent (T ∪ {ψ})) ∨ (is_consistent (T ∪ {∼ ψ}))
:=
begin
simp*,
by_contra,
rename a hc,
simp[is_consistent] at hc,
simp[not_or_distrib] at hc,
cases hc with hc1 hc2,
simp[is_consistent] at h,
destruct hc1,
sorry -- need to work with the proof system now... uh oh
-- looks like we need a lemma saying, given T ⊢ ψ, there exists a sentence ϕ such that ϕ ⊢ ψ.
-- (in any of the 8 cases, fold the internal and.intro over the context list)
end

/- Given a consistent theory T and sentence ψ, return whichever one of T ∪ ψ or T ∪ ∼ ψ is consistent. -/
noncomputable def extend {L : Language} (T : @Theory L) (ψ : @sentence L) (h : is_consistent T) : Σ' T : @Theory L, is_consistent T :=
dite (is_consistent $ T ∪ {ψ}) -- dependent if
     begin intro h1, exact psigma.mk (T ∪ {ψ}) h1 end -- then
     begin intro, have := can_extend T ψ h, rename this that, --else
                  have := @dne3 (is_consistent (T ∪ {ψ})) (is_consistent (T ∪ {∼ψ})) a,
                  refine psigma.mk (T ∪ {∼ ψ}) _,
                  rw[<-this],
                  assumption
                  end

/- We will need `extend` to show that the maximal theory given by Zorn's lemma is complete.

Now, we have to show that given an arbitrary chain in this poset, we can obtain an upper bound in this chain. We do this by taking the union.
-/


def theories_over (T : @Theory L) := {S : @Theory L // T ⊆ S}

open zorn

private lemma ex_coe {α : Type} (P : α → Prop) : (∃ x, P x) → (∃ x : α, true)
| ⟨a, b⟩ := ⟨a, trivial⟩


/-send a theory to a complete theory extending it-/
def completion_theory : @Theory L → @complete_Theory L :=
begin
intro T,
split,
swap,
refine classical.choice _,
refine nonempty_of_exists _,
exact λ x, true,  -- maybe want is_complete x ∧ is_consistent x instead of true?
refine ex_coe _ (@zorn (@Theory L) (set.subset) _ _),
  
  {sorry}, -- zorn's lemma hypothesis

  {intro, intro, intro, intro a_sub_b, intro b_sub_c,  -- set.subset is transitive
    simp[set.subset], simp[set.subset] at a_sub_b, simp[set.subset] at b_sub_c,
    intro,
    intro,
    have := a_sub_b a_2,
    have := b_sub_c this,
    assumption  },

  {sorry} -- end result is actually complete
end

end
