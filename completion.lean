/- Show that every theory can be extended to a complete theory -/

import .language_term_n2 order.zorn order.filter logic.basic
local attribute [instance] classical.prop_decidable
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
-- simp*,
by_contra,
rename a hc,
simp[is_consistent] at hc,
simp[not_or_distrib] at hc,
cases hc with hc1 hc2,
-- simp[is_consistent] at h,
apply h,
have hc_uno : T ⊢  ψ ⟹ s_falsum, sorry
-- need a deduction rule for sentences 
end

/- Given a consistent theory T and sentence ψ, return whichever one of T ∪ ψ or T ∪ ∼ ψ is consistent.  We will need `extend` to show that the maximal theory given by Zorn's lemma is complete. -/
noncomputable def extend {L : Language} (T : @Theory L) (ψ : @sentence L) (h : is_consistent T) : Σ' T : @Theory L, is_consistent T :=
dite (is_consistent $ T ∪ {ψ}) -- dependent if
     begin intro h1, exact psigma.mk (T ∪ {ψ}) h1 end -- then
     begin intro, have := can_extend T ψ h, rename this that, --else
                  have := @dne3 (is_consistent (T ∪ {ψ})) (is_consistent (T ∪ {∼ψ})) a,
                  refine psigma.mk (T ∪ {∼ ψ}) _,
                  rw[<-this],
                  assumption
                  end


/-
Now, we have to show that given an arbitrary chain in this poset, we can obtain an upper bound in this chain. We do this by taking the union.
-/

open zorn
private lemma ex_coe {α : Type} (P : α → Prop) : (∃ x, P x) → (∃ x : α, true)
| ⟨a, b⟩ := ⟨a, trivial⟩

/- Given a set of theories and a proof that they form a chain under set-inclusion, return their union and a proof that this contains every theory in the chain

-/

open classical

lemma subset_is_transitive {α : Type} : ∀ a b c : set α, a ⊆ b → b ⊆ c → a ⊆ c :=
begin intros a b c, intro a_sub_b, intro b_sub_c,
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

lemma nonempty_of_not_empty {α : Type} (a : set α) (h : ¬ a = ∅) : nonempty a :=
begin
simp*,
by_contra,
simp[not_exists_not] at a_1,
have : a = ∅,
refine funext _,
intro x,
refine propext _,
split,
apply a_1,
intro,
simp[has_emptyc.emptyc] at a_2,
exfalso, assumption,
contradiction
end

def Theory_over {L : Language} (T : @Theory L) (hT : is_consistent T): Type := {T' : @Theory L // T ⊆ T' ∧ is_consistent T'}

/- Every theory T is trivially a theory over itself -/
def over_self {L : Language} (T : @Theory L) (hT : is_consistent T): Theory_over T hT:=
begin
refine ⟨T, _⟩,
split, trivial, trivial
end


def Theory_over_subset {L : Language} {T : @Theory L} {hT : is_consistent T} : Theory_over T hT → Theory_over T hT→ Prop
:= λ T1 T2, T1.val ⊆ T2.val

instance {T : @Theory L} {hT : is_consistent T} : has_subset (Theory_over T hT) := ⟨Theory_over_subset⟩

instance {T : @Theory L} {hT : is_consistent T} : nonempty (Theory_over T hT) := ⟨over_self T hT⟩

/- Given a set of theories over T and a proof that they form a chain under set-inclusion,
return their union and a proof that this contains every theory in the chain

We need an extra case to handle the case where the chain is empty. This is the third argument, which will be the default return value.
-/

/-- Given T ⊢ ψ, return the finite context from T required to prove ψ, and a proof of this --/
def proof_finite_support {L : Language} (T : @Theory L) (ψ : @sentence L) (hψ : T ⊢ ψ) : Σ' Γ : finset (@sentence L), {ϕ : @sentence L | ϕ ∈ Γ} ⊢ ψ :=
sorry

def provable_of_provable_from_subset {L : Language} (T : @Theory L) (T' : @Theory L) (h_sub : T' ⊆ T) (ψ : @sentence L) (hψ : T' ⊢ ψ) : T ⊢ ψ :=
sorry


lemma consis_limit {L : Language} {T : @Theory L} {hT : is_consistent T} (Ts : set (Theory_over T hT)) (h_chain : chain Theory_over_subset Ts) : is_consistent (T ∪ set.sUnion (subtype.val '' Ts)) :=
begin -- so _here_ is where we need that proofs are finitely supported
unfold is_consistent,
intro h_inconsis,
let Γpair := proof_finite_support (T ∪ ⋃₀(subtype.val '' Ts)) ⊥ h_inconsis,
have h_bad : ∃ T' : (@Theory L), (T' ∈ (subtype.val '' Ts)) ∧ {ψ | ψ ∈ Γpair.fst} ⊆ T',
{sorry},
let T_bad := @strong_indefinite_description (@Theory L) (λ S, S ∈ (subtype.val '' Ts) ∧ ({ϕ | ϕ ∈ Γpair.fst} ⊆ S))  begin apply_instance end,
have T_bad_inconsis : sprovable T_bad.val ⊥,
fapply provable_of_provable_from_subset T_bad.val {ϕ | ϕ ∈ Γpair.fst},
exact (T_bad.property h_bad).right,
exact Γpair.snd,
have T_bad_consis : is_consistent T_bad.val,
{sorry},
contradiction
end

def limit_theory2 {L : Language} {T : @Theory L} {hT : is_consistent T} (Ts : set (Theory_over T hT)) (h_chain : chain Theory_over_subset Ts) : Σ' T : Theory_over T hT, ∀ T' ∈ Ts, T' ⊆ T :=
begin
refine ⟨⟨T ∪ set.sUnion (subtype.val '' Ts), _⟩, _⟩,
simp*,
intro,
sorry, -- just need to show that the union of consistent theories is consistent
intros T' hT' ψ hψ,
right, split, swap,
exact T'.val,
apply exists.intro, swap, exact hψ,
simp*,
exact T'.property
end

/- Given a theory T, show that the poset of theories over T satisfies the hypotheses of Zorn's lemma -/

lemma can_use_zorn2 {L : Language} {T : @Theory L} {hT : is_consistent T}  : (∀c, @chain (Theory_over T hT) Theory_over_subset c → ∃ub, ∀a∈c, a ⊆ ub) ∧ (∀(a b c : Theory_over T hT), a ⊆ b → b ⊆ c → a ⊆ c) :=
begin
  split,
  intro Ts, intro h_chain, let S := limit_theory2 Ts h_chain,
  let T_infty := S.fst,
  let H_infty := S.snd,
  refine exists.intro _ _,
  exact T_infty,
  intro T',
  intro H',
  have := H_infty T' H',
  simp[S, has_subset.subset] at this,
  simp[S],
  simp*,
  unfold has_subset.subset,
  intros a b c a_sub_b  b_sub_c,
    simp[Theory_over_subset], simp[Theory_over_subset] at a_sub_b, simp[Theory_over_subset] at b_sub_c,
    intros ψ hψ,
    have := a_sub_b hψ,
    have := b_sub_c this,
    assumption,
end

open classical


/- Given a consistent theory T, return a maximal extension of it given by Zorn's lemma, along with the proof that it is consistent and maximal -/
noncomputable def maximal_extension2 (L : Language) (T : @Theory L) (hT : is_consistent T)  : Σ' (T_max : Theory_over T hT), ∀ T' : Theory_over T hT, T_max ⊆ T' → T' ⊆ T_max :=
begin
let X := strong_indefinite_description (λ T_max : Theory_over T hT, ∀ T' : Theory_over T hT, T_max ⊆ T' → T' ⊆ T_max ) begin apply_instance end,
have := @can_use_zorn2 L T, rename this h_can_use,
have := zorn h_can_use.left h_can_use.right, rename this h_zorn,
let T_max := X.val,
let H := X.property,
split, swap,
exact T_max,
exact H h_zorn
end

lemma cannot_extend_maximal_extension2 {L : Language} {T : @Theory L} {hT : is_consistent T} (T_max' : Σ' (T_max : Theory_over T hT), ∀ T' : @Theory_over L T hT, T_max ⊆ T' → T' ⊆ T_max) (ψ : @sentence L) (H : is_consistent (T_max'.fst.val ∪ {ψ}))(H1 : ψ ∉ T_max'.fst.val) : false :=
begin
  let T_bad : Theory_over T hT,
  {refine ⟨T_max'.fst.val ∪ {ψ}, _⟩,
  split,
  simp[has_subset.subset],
  intro ψ, intro hψT,
  dedup,
  have extension_assumption := T_max'.fst.property.left,
  simp[has_insert.insert],
  apply or.inr,
  apply extension_assumption, assumption,
  assumption  },
  have h_max := T_max'.snd,
  have h_bad := h_max T_bad,
  have h_bad_ante : T_max'.fst ⊆ T_bad,
  intros ϕ hϕ,
  simp*,
  have h_bad_cons := h_bad h_bad_ante,
  simp[has_subset.subset, Theory_over_subset] at h_bad_cons,
  have h_bad_ψ : ψ ∈ (T_max'.fst.val),
  apply h_bad_cons,
  simp[has_insert.insert],
  have uh_oh := and.intro H1 h_bad_ψ,
  have := (not_and_self_iff (ψ ∈T_max'.fst.val)),
  cases this,
  exact this_mp uh_oh,
end

lemma q_of_not_p (p q : Prop) (h1 : p ∨ q) (h2 : ¬ p) : q := by tauto
/- Given a maximal consistent extension of consistent theory T, show it is complete -/
lemma complete_maximal_extension2_of_consis {L : Language} {T : @Theory L} {hT : is_consistent T}: @is_complete L (@maximal_extension2 L T hT).fst.val :=
begin
split,
exact (@maximal_extension2 L T hT).fst.property.right,
intro ψ,
by_cases ψ ∈ (@maximal_extension2 L T hT).fst.val,
exact or.inl h,
apply or.inr,
by_contra,
have can_extend := @can_extend L (@maximal_extension2 L T hT).fst.val ψ (@maximal_extension2 L T hT).fst.property.right,
have h_max := (@maximal_extension2 L T hT).snd,

by_cases is_consistent ((@maximal_extension2 L T hT).fst.val ∪ {ψ}),
  {rename h h1,
  refine cannot_extend_maximal_extension2 _ _ _ _,
  exact L, exact T, exact hT, exact maximal_extension2 L T hT, exact ψ,
  exact h1, exact h
  },
{rename h h2,
have h2' := q_of_not_p _ _ can_extend h2,
  fapply cannot_extend_maximal_extension2,
  exact L, exact T, exact hT, exact maximal_extension2 L T hT, exact ∼ψ,
    assumption, assumption
}
end


/- Given a consistent theory, return a complete extension of it -/
noncomputable def completion_theory3 : Π ( T : @Theory L) (h_consis : is_consistent T), Σ' T' : (@Theory_over L T h_consis), is_complete T'.val :=
begin
intro T,
intro h_consis,
let T_max := maximal_extension2 L T h_consis,
refine ⟨T_max.fst, _⟩,
apply complete_maximal_extension2_of_consis
end

end
