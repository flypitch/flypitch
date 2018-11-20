/- Show that every theory can be extended to a complete theory -/

import .fol .compactness order.zorn order.filter logic.basic data.finset data.set tactic.tidy data.list

local attribute [instance, priority 0] classical.prop_decidable
open fol

universe variables u v
section
parameter L : Language.{u}

lemma dne {p : Prop} (H : ¬¬p) : p :=
classical.by_contradiction H

lemma dne2 {p : Prop} : p = ¬ ¬ p :=
by {refine propext _, split, intro, exact (λ (h : ¬ p), absurd a h), intro a, exact dne a}

lemma dne3 {p q : Prop} (h : ¬ p) : (p ∨ q) = q :=
by {apply propext, split, swap, intro a, exact or.inr a, intro,
  fapply or.elim a, intro a', refine absurd h _, exact absurd a' h, exact id}

open classical
noncomputable def instantiate_existential {α : Type*} {P : α → Prop} (h : ∃ x : α, P x) : nonempty α → {x // P x} :=
  by {intro h_nonempty, let X := (@strong_indefinite_description α P h_nonempty), refine ⟨X.val, _⟩, apply X.property, exact h}


/-- Given a theory T and a sentence ψ, either T ∪ {ψ} or T ∪ {∼ ψ} is consistent.--/
lemma can_extend {L : Language} (T : Theory L) (ψ : sentence L) (h : is_consistent T): (is_consistent (T ∪ {ψ})) ∨ (is_consistent (T ∪ {∼ ψ}))
:=
begin
  simp[is_consistent],  by_contra,  rename a hc, rw[not_or_distrib] at hc,
  cases hc with hc1 hc2,
  apply h, rw [dne2.symm] at hc1, rw [dne2.symm] at hc2,
  have hc_uno : T ⊢'  ∼ψ,
    exact hc1.map simpI,
  have hc_dos : T ⊢' ∼∼ψ,
    exact hc2.map simpI,
  exact hc_dos.map2 (impE _) hc_uno
end

/- Given a consistent theory T and sentence ψ, return whichever one of T ∪ ψ or T ∪ ∼ ψ is consistent.  We will need `extend` to show that the maximal theory given by Zorn's lemma is complete. -/
noncomputable def extend {L : Language.{u}} (T : Theory L) (ψ : sentence L) (h : is_consistent T) : Σ' T : Theory L, is_consistent T :=
dite (is_consistent $ T ∪ {ψ}) -- dependent if
     begin intro h1, exact psigma.mk (T ∪ {ψ}) h1 end -- then
     begin intro, have := can_extend T ψ h, rename this that, --else
                  have := @dne3 (is_consistent (T ∪ {ψ})) (is_consistent (T ∪ {∼ψ})) a,
                  refine psigma.mk (T ∪ {∼ ψ}) _,
                  rw[<-this],
                  assumption end


/-
Now, we have to show that given an arbitrary chain in this poset, we can obtain an upper bound in this chain. We do this by taking the union.
-/

open zorn

/- Given a set of theories and a proof that they form a chain under set-inclusion, return their union and a proof that this contains every theory in the chain
-/

lemma subset_is_transitive {α : Type u} : ∀ a b c : set α, a ⊆ b → b ⊆ c → a ⊆ c
:= by tidy

private def subset_is_transitive_map {α : Type u} (a b c : set α) (h_ab : a ⊆ b) (h_bc : b ⊆ c) (x : α) (h : x ∈ a) :(x ∈ c)
:= by tidy

lemma nonempty_of_not_empty {α : Type u} (a : set α) (h : ¬ a = ∅) : nonempty a :=
begin
  by_contra, simp[not_exists_not] at a_1,  have : a = ∅,  refine funext _,  intro x,
  refine propext _,  split,  apply a_1,  intro, 
  exfalso, assumption,  contradiction
end

/-- Theory_over T is the subtype of Theory L consisting of consistent theories T' such that T' ⊇ T--/
def Theory_over {L : Language.{u}} (T : Theory L) (hT : is_consistent T): Type u := 
{T' : Theory L // T ⊆ T' ∧ is_consistent T'}

/-- Every theory T is trivially a theory over itself --/
def over_self {L : Language} (T : Theory L) (hT : is_consistent T): Theory_over T hT:=
  by {refine ⟨T, _⟩, split, trivial, assumption}

/-- Given two consistent theories T₁ and T₂ over T, say that T₁ ⊆ T₂ if T₁ ⊆ T₂--/
def Theory_over_subset {L : Language.{u}} {T : Theory L} {hT : is_consistent T} : Theory_over T hT → Theory_over T hT→ Prop
:= λ T1 T2, T1.val ⊆ T2.val

instance {T : Theory L} {hT : is_consistent T} : has_subset (Theory_over T hT) := ⟨Theory_over_subset⟩

instance {T : Theory L} {hT : is_consistent T} : nonempty (Theory_over T hT) := ⟨over_self T hT⟩


/- Given a sentence and the hypothesis that ψ is provable from a theory T, return a list of sentences from T and a proof that this list proves ψ -/
noncomputable def theory_proof_compactness' {L : Language} (T : Theory L) (ψ : sentence L) (hψ : T ⊢' ψ) : Σ' Γ : list (sentence L), {ϕ : sentence L | ϕ ∈ Γ} ⊢' ψ ∧ {ϕ : sentence L | ϕ ∈ Γ} ⊆ T :=
begin
  apply psigma_of_exists,
  rcases theory_proof_compactness hψ with ⟨Γ, H, K⟩,
  cases Γ with Γ hΓ, induction Γ, swap, refl,
  exact ⟨Γ, H, K⟩
end


def provable_of_provable_from_subset {L : Language} (T : Theory L) (T' : Theory L) (h_sub : T' ⊆ T) (ψ : sentence L) (proof : T' ⊢ ψ) : (T ⊢ ψ)
 :=
begin
fapply weakening,
exact T'.fst, fapply set.image_subset, assumption,
assumption
end

/- Given a chain of sets with nonempty union, conclude that the chain is nonempty-/
def nonempty_chain_of_nonempty_union {α : Type u} {A_i : set $ set α} {h_chain : chain set.subset A_i} (h : nonempty $ set.sUnion A_i) : nonempty A_i :=
begin
have a := classical.choice h,
cases a with a_val a_property, unfold set.sUnion at a_property, simp at a_property,
cases a_property with A hA, simp, fapply exists.intro, exact A, exact hA.left
end

/- Given two elements in a chain of sets over T, their union over T is in the chain -/
lemma in_chain_of_union {α : Type u} (T : set α) (A_i : set $ set α) (h_chain : chain set.subset A_i) (as : list A_i) (h_over_T : ∀ A ∈ A_i, T ⊆ A) (A1 A2 ∈ A_i) : A1 ∪ A2 = A1 ∨ A1 ∪ A2 = A2 :=
begin
dedup,
unfold has_union.union set.union has_mem.mem set.mem,
unfold chain set.pairwise_on at h_chain,
by_cases A1 = A2,
  simp*, finish,
  have := h_chain A1 H A2 H_1 h, cases this,
  {fapply or.inr, apply funext, intro x, apply propext, split,
  intro h1, have : A1 x ∨ A2 x, by assumption, fapply or.elim, exact A1 x, exact A2 x, assumption, intro hx, dedup, unfold set.subset at this, exact this hx, finish,
  intro hx, apply or.inr, assumption},

  {fapply or.inl, apply funext, intro x, apply propext, split,
  intro hx, have : A1 x ∨ A2 x, by assumption, fapply or.elim, exact A2 x, exact A1 x, finish, intro h2x, dedup, unfold set.subset at this, exact this h2x, finish,
intro h3x, apply or.inl, assumption}
end

/--Given a chain and two elements from this chain, return their maximum. --/
noncomputable def max_in_chain {α : Type u} {R : α → α → Prop} {Ts : set α} {nonempty_Ts : nonempty Ts} (h_chain : chain R Ts) (S1 S2 : α) (h_S1 : S1 ∈ Ts) (h_S2 : S2 ∈ Ts) : Σ' (S : α), (S = S1 ∧ (R S2 S1 ∨ S1 = S2)) ∨ (S = S2 ∧ (R S1 S2 ∨ S1 = S2)) :=
begin
  unfold chain set.pairwise_on at h_chain,
  have := h_chain S1 h_S1 S2 h_S2,
  by_cases S1 = S2,

    refine ⟨S1, _ ⟩, fapply or.inl, fapply and.intro, exact rfl, exact or.inr h,
    
    have H := this h,
    by_cases R S1 S2,
      refine ⟨S2, _⟩, fapply or.inr, refine and.intro rfl _, exact or.inl h,

      tactic.unfreeze_local_instances, dedup, simp[*, -H] at H, refine ⟨S1, _⟩, fapply or.inl,
      refine and.intro rfl _, exact or.inl H
end

/--Given a nonempty chain under a transitive relation and a list of elements from this chain, return an upper bound, with the maximum of the empty list defined to be the witness to the nonempty --/
noncomputable def max_of_list_in_chain {α : Type u} {R : α → α → Prop} {trans : ∀{a b c}, R a b → R b c → R a c} {Ts : set α} {nonempty_Ts : nonempty Ts} (h_chain : chain R Ts) (Ss : list α) -- {nonempty_Ss : nonempty {S | S ∈ Ss}}
(h_fs : ∀ S ∈ Ss, S ∈ Ts) : Σ' (S : α), S ∈ Ts ∧ (∀ S' ∈ Ss, S' = S ∨ R S' S) :=
begin
  tactic.unfreeze_local_instances,
  induction Ss, have := classical.choice nonempty_Ts, split, simp, swap, exact this.val, exact this.property, 

    by_cases nonempty {S | S ∈ Ss_tl},
      swap, simp[*,-h] at h, refine ⟨Ss_hd, _⟩, simp*, --  fapply and.intro, constructor, refl,
      -- intros S' hS', cases hS', fapply or.inl, assumption, exfalso, have := h S', contradiction,

      have actual_ih := Ss_ih,
      let tl_max :=
        begin refine actual_ih _, intros S hS, fapply h_fs, fapply or.inr, assumption end,
      have pairwise_max := max_in_chain h_chain Ss_hd tl_max.fst
begin fapply h_fs, constructor, refl end begin have := tl_max.snd, exact this.left  end,
      
      split, swap, exact pairwise_max.fst, fapply and.intro,
      have h_max := pairwise_max.snd, cases h_max with h_max1 h_max2,
      simp*, rw[h_max2.left], exact tl_max.snd.left, 
      swap, assumption,
      intros S' hS', cases hS' with h_left h_right,
      have h_max := pairwise_max.snd, cases h_max with h_max1 h_max2,
      fapply or.inl, have := h_max1.left, cc,
      have := h_max2.right, cases this with h1 h2,
      repeat{simp*},
      have h_max := pairwise_max.snd, cases h_max with h_max1 h_max2,
      all_goals{simp*},
      swap,
      have this1 : S' = tl_max.fst ∨ R S' tl_max.fst,
        have this2 := tl_max.snd.right S' h_right,
        cases this2 with this2_left this2_right,
        exact or.inl this2_left,
        exact or.inr this2_right,
      exact this1,

      have : ∀(S : α), S ∈ Ss_tl → S ∈ Ts,
        begin
          intros S hS, fapply h_fs, exact or.inr hS
        end,
      
      have almost_there := (actual_ih this).snd.right S' h_right,
      cases almost_there with almost_there_1 almost_there_2,
      simp*, cases h_max1 with H1 H2, simp[*, -H2] at H2,
        cases H2, exact or.inr H2, rw[H2], finish,

      cases h_max1 with H1 H2, simp[*,-H2] at H2, fapply or.inr,
      have H_ab : R S' tl_max.fst, exact almost_there_2,
      cases H2 with A1 A2,
        exact trans H_ab A1,
        rw[A2], exact H_ab
end 

/-- Given a xs : list α, it is naturally a list {x ∈ α | x ∈ xs} --/
def list_is_list_of_subtype : Π(α : Type u), Π (fs : list α),  Σ' xs : list ↥{f : α | f ∈ fs}, ∀ f, ∀ h : f ∈ fs, (⟨f,h⟩ : ↥{f : α | f ∈ fs}) ∈ xs
| L [] := begin simp*,  split, exact [], trivial end
| L (list.cons hd tl) :=
  begin
    refine ⟨_, _⟩,
    have ih := list_is_list_of_subtype L tl,
    have F : {f | f ∈ tl} → {f | f ∈ list.cons hd tl},
    intro f, refine ⟨f, _⟩, fapply or.inr, exact f.property,
    have ih_image := list.map F ih.fst,
    refine _::(ih_image),
    split, swap, exact hd, exact or.inl rfl,
    intros f hf, simp [*, -sigma.exists],
    cases hf, exact or.inl hf,
    fapply or.inr, fapply exists.intro, exact hf, exact (list_is_list_of_subtype L tl).snd f hf
  end

/-- The limit theory of a chain of consistent theories over T is consistent --/
lemma consis_limit {L : Language} {T : Theory L} {hT : is_consistent T} (Ts : set (Theory_over T hT)) (h_chain : chain Theory_over_subset Ts) : is_consistent (T ∪ set.sUnion (subtype.val '' Ts)) :=
begin -- so _here_ is where we need that proofs are finitely supported
  intro h_inconsis,
  by_cases nonempty Ts, swap,
    { simp* at h, simp[*, -h_inconsis] at h_inconsis, unfold is_consistent at hT, exact hT h_inconsis},

  have Γpair := theory_proof_compactness' (T ∪ ⋃₀(subtype.val '' Ts)) ⊥ h_inconsis,
  have h_bad : ∃ T' : (Theory L), (T' ∈ (subtype.val '' Ts)) ∧ {ψ | ψ ∈ Γpair.fst} ⊆ T',

 
 {cases Γpair with fs Hfs, rename h hTs,
  have dSs : Π f ∈ fs, Σ' S_f : (Theory_over T hT), set.mem S_f Ts ∧ (set.mem (f) (S_f.val)), -- to each f in fs, associate an S_f containing f from the chain
    {  intros f hf, have H := Hfs.right,
  unfold set.image set.sUnion set.subset set.mem list.mem at H,
  have H' := H hf,  by_cases f ∈ T,
  split, swap, {exact (classical.choice hTs).val},
  {fapply and.intro, exact (choice hTs).property,
    have H := (choice hTs).val.property.left,
    exact H h},
 
    simp[*, -H'] at H',
    have witness := instantiate_existential H' begin fapply nonempty.intro, exact T end, simp* at witness,
    split, swap, split, swap, exact witness.val, cases witness.property with case1 case2, cases case1 with case1' case1'', exact case1',
split, have witness_property := witness.property, cases witness_property with case1 case2, cases case1 with case1' case1'', exact case1'',
have witness_property := witness.property, cases witness_property with case1 case2, exact case2,},

  have T_max : Σ' (T_max : Theory_over T hT), (T_max ∈ Ts) ∧ ∀ ψ ∈ fs, (ψ) ∈ T_max.val,  -- get the theory and a proof that it contains all the f
    {  let F : {f | f ∈ fs} → Theory_over T hT :=
    begin intro f, exact (dSs f.val f.property).fst end,
 let fs_list_subtype := list_is_list_of_subtype _ fs,
 let T_list : list (Theory_over T hT) :=
    begin fapply list.map F, exact fs_list_subtype.fst end,
  have T_list_subset_Ts : (∀ (S : Theory_over T hT), S ∈ T_list → S ∈ Ts),
    intro S, simp [-sigma.exists, -sigma.forall], intros x h1 h2, simp [*,-h2] at h2, rw[<-h2.right],
    have := (dSs x h1).snd.left, assumption,

  have max_of_list := max_of_list_in_chain h_chain T_list T_list_subset_Ts,
  split, swap,
    {exact max_of_list.fst},
    {split, exact max_of_list.snd.left, 
      {intros f hf,
        have almost_there : f ∈ (F ⟨f, begin simpa end⟩).val, simp*, exact (dSs f hf).snd.right,
        have nearly_there : (F ⟨f, begin simpa end⟩) ⊆ max_of_list.fst,
          have := max_of_list.snd.right (F ⟨f, begin simpa end⟩),
          have so_close : F ⟨f, _⟩ = max_of_list.fst ∨ Theory_over_subset (F ⟨f, _⟩) (max_of_list.fst),
            begin
            refine this _, simp [*, -sigma.exists], fapply exists.intro, exact f, fapply exists.intro,
            exact hf, fapply and.intro, unfold has_mem.mem list.mem,
            {apply fs_list_subtype.snd},
            {refl},
            end,
        cases so_close with case1 case2,
        rw[case1], intros a h, exact h,
        exact case2,
        exact nearly_there almost_there,
        },
      },
    {intros a b c, unfold Theory_over_subset, fapply subset_is_transitive},
    {assumption},},
  
  fapply exists.intro, exact T_max.fst.val,
  fapply and.intro, fapply set.mem_image_of_mem, exact T_max.snd.left,
  have := T_max.snd.right, intros ψ hψ, exact this ψ hψ},

  let T_bad := @strong_indefinite_description (Theory L) (λ S, S ∈ (subtype.val '' Ts) ∧ ({ϕ | ϕ ∈ Γpair.fst} ⊆ S))  begin apply_instance end,
  have T_bad_inconsis : sprovable T_bad.val ⊥,
  fapply nonempty.intro,
  fapply provable_of_provable_from_subset T_bad.val {ϕ | ϕ ∈ Γpair.fst},
  exact (T_bad.property h_bad).right,
  exact classical.choice Γpair.snd.left,
  have T_bad_consis : is_consistent T_bad.val,
    {have almost_done := (T_bad.property h_bad).left,
    simp[set.image] at almost_done,
    cases almost_done,
    exact almost_done_w.right},
    exact T_bad_consis T_bad_inconsis, 
end

--refine @exists.elim ( T ⊆ T_bad.val ∧ is_consistent (T_bad.val)) (λ x :  T ⊆ T_bad.val ∧ is_consistent (T_bad.val), ⟨_, x⟩ ∈ Ts), swap},



/-- Given a chain of consistent extensions of a theory T, return the union of those theories and a proof that this is a consistent extension of T --/
def limit_theory {L : Language} {T : Theory L} {hT : is_consistent T} (Ts : set (Theory_over T hT)) (h_chain : chain Theory_over_subset Ts) : Σ' T : Theory_over T hT, ∀ T' ∈ Ts, T' ⊆ T :=
begin
refine ⟨⟨T ∪ set.sUnion (subtype.val '' Ts), _⟩, _⟩, simp*, intro,
exact @consis_limit L T hT Ts h_chain begin simp* end,
intros T' hT' ψ hψ, right, split, swap, exact T'.val,
apply exists.intro, swap, exact hψ, simp*, exact T'.property
end

/-- Given a theory T, show that the poset of theories over T satisfies the hypotheses of Zorn's lemma --/
lemma can_use_zorn {L : Language.{u}} {T : Theory L} {hT : is_consistent T}  : (∀c, @chain (Theory_over T hT) Theory_over_subset c → ∃ub, ∀a∈c, a ⊆ ub) ∧ (∀(a b c : Theory_over T hT), a ⊆ b → b ⊆ c → a ⊆ c) :=
begin
  split,  intro Ts, intro h_chain, let S := limit_theory Ts h_chain,
  let T_infty := S.fst,  let H_infty := S.snd,
  refine exists.intro _ _,  exact T_infty, intro T', intro H',
  finish, tidy
end

/-- Given a consistent theory T, return a maximal extension of it given by Zorn's lemma, along with the proof that it is consistent and maximal --/
noncomputable def maximal_extension (L : Language.{u}) (T : Theory L) (hT : is_consistent T) : 
  Σ' (T_max : Theory_over T hT), ∀ T' : Theory_over T hT, T_max ⊆ T' → T' ⊆ T_max :=
begin
  let X := strong_indefinite_description (λ T_max : Theory_over T hT, ∀ T' : Theory_over T hT, T_max ⊆ T' → T' ⊆ T_max ) begin apply_instance end,
  have := @can_use_zorn L T, rename this h_can_use,
  have := zorn h_can_use.left h_can_use.right, rename this h_zorn,
  let T_max := X.val, let H := X.property,
  exact ⟨T_max, H h_zorn⟩,
end

/-- The maximal extension returned by maximal_extension cannot be extended. --/
lemma cannot_extend_maximal_extension {L : Language} {T : Theory L} {hT : is_consistent T} (T_max' : Σ' (T_max : Theory_over T hT), ∀ T' : Theory_over T hT, T_max ⊆ T' → T' ⊆ T_max) (ψ : sentence L) (H : is_consistent (T_max'.fst.val ∪ {ψ}))(H1 : ψ ∉ T_max'.fst.val) : false :=
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

/-- Given a maximal consistent extension of consistent theory T, show it is complete --/
lemma complete_maximal_extension_of_consis {L : Language} {T : Theory L} {hT : is_consistent T}: @is_complete L (@maximal_extension L T hT).fst.val :=
begin
  refine ⟨(@maximal_extension L T hT).fst.property.right, _⟩,
  intro ψ, by_cases ψ ∈ (@maximal_extension L T hT).fst.val, exact or.inl h,
  apply or.inr,
  by_contra,
  have can_extend := @can_extend L (@maximal_extension L T hT).fst.val ψ (@maximal_extension L T hT).fst.property.right,
  have h_max := (@maximal_extension L T hT).snd,

  by_cases is_consistent ((@maximal_extension L T hT).fst.val ∪ {ψ}),
    {rename h h1,
      fapply cannot_extend_maximal_extension, repeat{assumption}},
  {rename h h2,
  have q_of_not_p : ∀ p q : Prop, ∀ h1 : p ∨ q, ∀ h2 : ¬ p, q, by tauto,
  have h2' := q_of_not_p _ _ can_extend h2,
  fapply cannot_extend_maximal_extension, exact L, exact T, exact hT, exact maximal_extension L T hT, exact ∼ψ, repeat{assumption}},
end


/-- Given a consistent theory, return a complete extension of it --/
noncomputable def completion_of_consis : Π ( T : Theory L) (h_consis : is_consistent T), Σ' T' : (Theory_over T h_consis), is_complete T'.val :=
begin
  intros T h_consis,
  let T_max := maximal_extension L T h_consis,
  exact ⟨T_max.fst, by apply complete_maximal_extension_of_consis⟩,
end

end
