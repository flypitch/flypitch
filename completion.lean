/- Show that every theory can be extended to a complete theory -/

import .language_term_n2 order.zorn order.filter logic.basic
attribute [instance, priority 0] classical.prop_decidable
open fol

section
parameter L : Language

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



open zorn
private lemma ex_coe {α : Type} (P : α → Prop) : (∃ x, P x) → (∃ x : α, true)
| ⟨a, b⟩ := ⟨a, trivial⟩

/- Given a set of theories and a proof that they form a chain under set-inclusion,
return their union and a proof that this contains every theory in the chain

We need an extra case to handle the case where the chain is empty. This is the third argument, which will be the default return value.
-/
noncomputable def limit_theory {L : Language} (Ts : set $ @Theory L) (h_chain : chain set.subset Ts) (T : @Theory L) : Σ' T : @Theory L, ∀ T' ∈ Ts, T' ⊆ T :=
dite (Ts = ∅) -- dependent if

     (begin intro, split, swap, -- then
      exact T, intro, intro hc,
      exfalso, simp[a] at hc,
     assumption end)

     (begin intro, split, swap, -- else
     exact set.sUnion Ts,
     intro T',
     simp[set.sUnion],
     intros h ψ h1,
     simp*,
     refine exists.intro _ _,
     exact T',
     refine and.intro _ _,
     assumption, assumption
     end)
 
     -- (begin,
     -- split, swap,
     -- exact set.sUnion Ts,
     -- intro T',
     -- simp[set.sUnion],
     -- intros h ψ h1,
     -- simp*,
     -- refine exists.intro _ _,
     -- exact T',
     -- refine and.intro _ _,
     -- assumption, assumption
     -- end)

--def duh_coe (Ts : set $ @Theory L) (h_chain : chain set.subset Ts) : (limit_theory Ts h_chain) → (@Theory L)

lemma limit_theory_of_empty_is_T {L : Language} (Ts : set $ @Theory L) (h_chain : chain set.subset Ts) (T : @Theory L) (h : Ts = ∅) : (limit_theory Ts h_chain T).fst = T
:= begin
unfold limit_theory,
simp*
end

lemma subset_is_transitive {α : Type} : ∀ a b c : set α, a ⊆ b → b ⊆ c → a ⊆ c :=
begin intro, intro, intro, intro a_sub_b, intro b_sub_c,  -- set.subset is transitive, another argument to zorn
--    unfold (a ⊆ c), simp[set.subset] at a_sub_b, simp[set.subset] at b_sub_c,
    intro,
    intro,
    have := a_sub_b a_2,
    have := b_sub_c this,
    assumption
end

private def subset_is_transitive_map {α : Type} (a b c : set α) (h_ab : a ⊆ b) (h_bc : b ⊆ c) (x : α) (h : x ∈ a) : (x ∈ c) :=
begin
rename h x_in_a,
have := subset_is_transitive a b c h_ab h_bc,
have := this x_in_a, assumption
end

def Theory_over {L : Language} (T : @Theory L) : Type := {T' : @Theory L // T ⊆ T'}

/-Send a theory T to a theory T' extending T, with a proof that T' is complete-/
def completion_theory : Π (T : @Theory L), Σ' T' : (@Theory_over L T), is_complete T'.val :=
begin
intro T,
split,
swap,
refine classical.choice _,
refine nonempty_of_exists _,
exact λ x, true,  -- maybe want is_complete x ∧ is_consistent x instead of true?
refine ex_coe _ (@zorn (@Theory_over L T) (λ T1 T2, T1.val ⊆ T2.val) _ _),  
/- Hypotheses of Zorn's lemma -/
  {intro Ts,
    intro h_chain,
    have : chain set.subset ((λ x : Theory_over T, x.val) '' Ts),
      {simp[chain], simp[chain] at h_chain,
        simp[set.pairwise_on], simp[set.pairwise_on] at h_chain,
        intros T1 h1 h1' h_T1_coh T2 h2 h2' h_T2_coh h_neq,           
        have : ¬ (h1 = h2),
          {by_contra,
          have : h1.val = h2.val,
          simp*,
          cc}, rename this neq_lift,
        have := h_chain h1 h1' h2 h2' neq_lift, rename this chain_lift,
        rw[h_T1_coh, h_T2_coh] at chain_lift,
        assumption
        },
    rename this h'_chain,
    let Ts' := ((λ x : Theory_over T, x.val) '' Ts),
    let T_infty := (limit_theory Ts' h'_chain T),
--    have := (limit_theory Ts h_chain) = T_infty, by refl,
    refine exists.intro _ _,
    {refine ⟨T_infty.fst, _⟩,
      intro,
      have := T_infty.snd, rename this P,      
      intro,
      by_cases (Ts' = ∅),
      {have : T_infty.fst = T,
       have := (limit_theory_of_empty_is_T Ts' h'_chain T h), rename this h1,
      have : (limit_theory Ts' h'_chain T).fst = T_infty.fst, by refl, by cc,
      rw[<-this] at a_1, assumption},
    refine subset_is_transitive_map T _ T_infty.fst _ _ _ _,
    {sorry},
    {sorry},
    {sorry},
    {assumption},
    },
simp*,
  intros A hA,
  intros ψ hψ,
  simp[limit_theory],
  by_cases Ts' = ∅,
swap,
{simp*,
sorry -- we again need to show that there exists a lift, and apply transitivity
},
{  simp*,
  exfalso,
 { have : A.val ∈ Ts', -- this case should be easy, just need to show that A cannot actually exist
admit},
    },
  {intro, intro, intro, intro a_sub_b, intro b_sub_c,  -- set.subset is transitive, another argument to zorn
    simp[set.subset], simp[set.subset] at a_sub_b, simp[set.subset] at b_sub_c,
    intro,
    intro,
    have := a_sub_b a_2,
    have := b_sub_c this,
    assumption  },

  {sorry} -- end result is actually complete
end

end
