import .fol order.zorn order.filter logic.basic data.finset data.set data.list .completeness
local attribute [instance, priority 0] classical.prop_decidable
open fol

universes u v

/- A simple consequence of weakening, needed for recursion below  -/
lemma weakening' {L : Language.{u}} {S_1 S_2 : set $ formula L} {ψ_1 ψ_2 : formula L} (p1 : S_1 ⊢ ψ_1) (p2 : S_2 ⊢ ψ_2) : (S_1 ∪ S_2 ⊢ ψ_1) × (S_1 ∪ S_2 ⊢ ψ_2) :=
  begin
    split, fapply @weakening L S_1 (S_1 ∪ S_2),
    simpa only [set.subset_union_left],
    fapply @weakening L S_2 (S_1 ∪ S_2), simpa only [set.subset_union_right]
  end

/-- Given an xs : list α, an x : α, a set T on α such that everything in xs which is not x is in T, return the sublist which excludes x, a proof that this list is now a subset of T, and a proof that everything in this list was not the forbidden element x. --/
noncomputable def list_except {α : Type u} (xs : list α) (x : α) (T : set α) (h : ∀ y ∈ xs, y ≠ x → y ∈ T) : Σ' ys : list α, ({ϕ | ϕ ∈ ys} ⊆ T ∧ (∀ y ∈ ys, y ≠ x)) ∧ (∀ y ∈ xs, y ≠ x → y ∈ ys) :=
begin
  induction xs generalizing h,
    split, swap, exact list.nil, simp,
    split, swap, refine if _ then _ else _,
    {exact xs_hd = x,},
    {apply_instance,},
    {refine (xs_ih _).fst, intros, fapply h, simp, exact or.inr H, assumption},
    {refine _::((xs_ih _).fst), exact xs_hd, intros, fapply h, simp, exact or.inr H, assumption},  -- finish ite statement
  split, split,
  
  by_cases xs_hd = x; simp only [*, list.mem_cons_iff, if_false]; intros a ha;
simp only [*, -ha, list.mem_cons_iff, set.mem_set_of_eq] at ha,
simp only [*, -ha, if_true, list.mem_cons_iff, eq_self_iff_true, set.mem_set_of_eq] at ha,
     {dedup, refine (xs_ih _).snd.left.left _, intros, fapply h, simp, exact or.inr H, assumption, assumption,},
     {dedup, cases ha, swap,
     refine (xs_ih _).snd.left.left _, intros, fapply h, simp, exact or.inr H, assumption, assumption, fapply h, fapply or.inl, assumption, cc},

    by_cases (xs_hd = x);
      simp only [*, true_and, list.mem_cons_iff, list.forall_mem_cons', if_false, ne.def, not_false_iff],
      intros y H, refine ((xs_ih _).snd).left.right _ _,
      intros, dedup, fapply h, simp only [list.mem_cons_iff], apply or.inr,
      repeat{assumption},
      simp only [if_true, list.mem_cons_iff, eq_self_iff_true] at H, assumption,
      
      intros y H, refine ((xs_ih _).snd).left.right _ _,
      intros, dedup, fapply h, simp, apply or.inr, assumption,
      assumption, assumption, 

    intro y, intro hy, by_cases xs_hd = x, simp only [*, if_true, list.mem_cons_iff, eq_self_iff_true, ne.def], 
    cases hy, intro h_bad, have : y = x, by cc, contradiction,
      
         {intro h_good, fapply (xs_ih _).snd.right y,
           exact hy, exact h_good},
         {intro h_good, simp only [*, list.mem_cons_iff, if_false], cases hy, exact or.inl hy, fapply or.inr, fapply (xs_ih _).snd.right y,
           exact hy, exact h_good},
end

open classical

/- Couldn't find this def in set.basic... sure it's around somewhere-/
/-- Given x ∈ f '' S, choose a lift x' in the preimage of x; return x' and a proof that x' is a lift --/
noncomputable def image_lift {α : Type u} {β : Type v} {f : α → β} {S : set α} (x ∈ f '' S) : Σ' (x' : α), x' ∈ S ∧ f x' = x :=
begin
  simp only [*, -H, set.mem_image] at H,
  have := strong_indefinite_description, swap, exact α,
  have prelift : {x_1 // (∃ (y : α), (λ (y : α), y ∈ S ∧ f y = x) y) → (λ (y : α), y ∈ S ∧ f y = x) x_1},
  fapply this (λ y, y ∈ S ∧ f y = x), fapply nonempty_of_exists, exact (λ y, y ∈ S ∧ f y = x),
  exact H, have snd := prelift.property, simp only [*, -snd, forall_prop_of_true] at snd,
  refine ⟨prelift.val, _⟩, exact snd,
end

/-- Given a list xs : list β, a set S : set α, a proof that {x | x ∈ xs} ⊆ f '' S, return a list of lifts ys : list α, a proof that ys ⊆ S and a proof that f '' ys = xs --/
noncomputable def image_lift_list {α : Type u} {β : Type v} {f : α → β} {S : set α} {xs : list β} (h_sub : {x | x ∈ xs} ⊆ f '' S) : Σ' (ys : list α), ({y' | y' ∈ ys} ⊆ S) ∧ f '' {y | y ∈ ys} = {x | x ∈ xs} :=
begin
  induction xs generalizing h_sub,
    split, swap,
      {exact list.nil},
      {fapply and.intro, repeat{simp}},
  
          let Hxs_ih : {x : β | x ∈ xs_tl} ⊆ f '' S :=
            begin intros x hx, fapply h_sub, exact or.inr hx end,
          let Himage_lift : xs_hd ∈ (f '' S) :=
            begin fapply h_sub, simp end,
            simp only [*, -Himage_lift, set.mem_image] at Himage_lift,
          split;
      
      let x_image_lift := begin fapply @image_lift α β f S xs_hd, exact Himage_lift end,
                        
    swap,
      have : {x : β | x ∈ xs_tl} ⊆ f '' S,
        {intros x hx, fapply h_sub, fapply or.inr, exact hx},
      have actual_ih := xs_ih this,
      let zs := actual_ih.fst, let h_zs := actual_ih.snd,
      refine _::zs, exact x_image_lift.fst,

      split,
        intros y Hy, cases Hy, rw[Hy], exact x_image_lift.snd.left,
        
        refine (xs_ih Hxs_ih).snd.left _,
          exact Hy,

        simp only [*, list.mem_cons_iff], fapply funext, intro x, fapply propext,

        split,
          intro hx, cases hx with hx_witness hx_hypothesis,

            cases hx_hypothesis with h1 h2,
            cases h1,
              have := (image_lift xs_hd Himage_lift).snd;
              fapply or.inl, rw[<-h2, h1], exact this.right,
              
              fapply or.inr, rw[<-h2],
              have h_final : f hx_witness ∈ f '' {y : α | y ∈ (xs_ih Hxs_ih).fst},
              fapply exists.intro, exact hx_witness, simpa,
              rw[(xs_ih Hxs_ih).snd.right] at h_final,
              exact h_final,

        intro hx, cases hx with h_hd h_tl,
           fapply exists.intro, exact x_image_lift.fst, rw[h_hd], simp,
           exact x_image_lift.snd.right, unfold set.image,
           
           have strong_lift := begin
                                   fapply strong_indefinite_description, exact α,
                                   exact λ a, a ∈ {y : α | y ∈ (xs_ih Hxs_ih).fst} ∧ f a = x,
                                   fapply nonempty_of_exists, exact λ x, x ∈ S ∧ f x = xs_hd,
                                   exact Himage_lift
                                  end;

           have h_almost := (xs_ih Hxs_ih).snd;
           have h_exists : x ∈ f '' {y : α | y ∈ (xs_ih Hxs_ih).fst},
              rw[h_almost.right], assumption, unfold set.image at h_exists;
           fapply exists.intro, 
                       
              exact strong_lift.val, fapply and.intro, fapply or.inr, refine (strong_lift.property _).left, exact h_exists, refine (strong_lift.property _).right, exact h_exists
end

set_option eqn_compiler.lemmas false

/-- Any proof from a set of formulas is provable from a finite subformulas. --/
noncomputable def proof_compactness {L : Language.{u}} : Π {ψ : formula L}, Π {T : set $ formula L},  Π (pψ : T ⊢ ψ), Σ Γ : list (formula L), Σ' p : {ϕ : formula L | ϕ ∈ Γ} ⊢ ψ, {ϕ : formula L | ϕ ∈ Γ} ⊆ T
| ψ T (axm a) := begin split, swap, exact [ψ],have : {ϕ : formula L | ϕ ∈ [ψ]} = {ψ},
                   by refl, split, rw[this],
                   fapply axm, simp, rw[this], simp, exact a
                   end
| B T (impE A P_AB P_A) :=
    begin
      have S1 := proof_compactness P_AB,
      have S2 := proof_compactness P_A,
      split, swap, exact S1.fst ∪ S2.fst,

      let T1 := {ϕ | ϕ ∈ S1.fst}, let T2 := {ϕ | ϕ ∈ S2.fst},
      have hT1 : T1 ⊢ A ⟹ B, have := S1.snd.fst, exact this,
      have hT2 : T2 ⊢ A, have := S2.snd.fst, exact this,
      have : (T1 ∪ T2) ⊢ (A ⟹ B) × T1 ∪ T2 ⊢ A,
        fapply weakening', exact hT1, exact hT2,
      
      split, simp only [*, list.mem_union], fapply impE, exact A,
      exact this.fst, exact this.snd,
      simp only [*, list.mem_union],intro ψ, intro hψ,
      cases hψ, fapply S1.snd.snd, exact hψ, fapply S2.snd.snd, exact hψ,
    end
| (f1 ⟹ f2) T (impI P) :=
  begin
    have S := (proof_compactness P),
    let S' := --Σ' (ys : list (formula L)), {ϕ : formula L | ϕ ∈ ys} ⊆ T ∧ ∀ (y : formula L), y ∈ ys → y ≠ f1,
      begin { refine (list_except S.fst f1 T _),
      have := (S.snd).snd, intros y H a, have := this H, cases this, exfalso, contradiction, assumption}, end,
    split, swap,  exact S'.fst, have hS' := S'.snd, 
    split, swap, exact hS'.left.left,
    fapply impI,
    have h_weakening : {ϕ : formula L | ϕ ∈ S.fst} ⊆ insert f1 {ϕ : formula L | ϕ ∈ S'.fst},
      {intro x, intro hx, simp, by_cases x = f1,
        exact or.inl h, simp only [*, false_or], fapply hS'.right, assumption, assumption},
    
    {fapply weakening, exact {ϕ : formula L | ϕ ∈ S.fst}, exact h_weakening, exact S.snd.fst}
  end
| A T (falsumE P) :=
  begin
    have S := (proof_compactness P),
    let S' := begin refine (list_except S.fst (∼A) T _),
                    have := (S.snd).snd, intros y H a,
                    have := this H,
                cases this, exfalso, contradiction, assumption
              end,
    refine ⟨S'.fst, _⟩, have hS' := S'.snd, 
    split, swap, exact hS'.left.left,
    fapply falsumE,
    have h_weakening : {ϕ : formula L | ϕ ∈ S.fst} ⊆ insert ∼A {ϕ : formula L | ϕ ∈ S'.fst},
      {intro x, intro hx, simp, by_cases x = ∼A,
        exact or.inl h, simp only [*, false_or], fapply hS'.right, assumption, assumption},
 
    {fapply weakening, exact {ϕ : formula L | ϕ ∈ S.fst}, exact h_weakening, exact S.snd.fst}  
  end
|  (∀' A) T (allI P) :=
  begin
    have S  := (proof_compactness P), have h_subset := S.snd.snd,
    have preS' := image_lift_list h_subset, let S' := preS'.fst, have hS' := preS'.snd,
    refine ⟨S', _⟩, refine ⟨_, hS'.left⟩, fapply allI,
    rw[hS'.right], exact S.snd.fst,
  end
| (_ ≃ t) T (ref _ _) :=
  begin
    dedup, refine ⟨[], _⟩, split, fapply fol.prf.ref,
    intro ψ, intro hψ, exfalso, exact hψ
  end
| .(_[_ // 0]) T (allE' A t P) :=
        begin
          have preS := proof_compactness P, split, swap, exact preS.fst,
          split, fapply allE', exact preS.snd.fst, exact preS.snd.snd
        end
| .(_[_ // 0]) T (subst' s t A P1 P2) :=
    begin
      have S1 := proof_compactness P1,
      have S2 := proof_compactness P2,
      split, swap, exact S1.fst ∪ S2.fst,

      let T1 := {ϕ | ϕ ∈ S1.fst}, let T2 := {ϕ | ϕ ∈ S2.fst},
      have hT1 : T1 ⊢ s ≃ t, have := S1.snd.fst, exact this,
      have hT2 : T2 ⊢ A[s // 0], have := S2.snd.fst, exact this,
      have : (T1 ∪ T2) ⊢ s ≃ t × T1 ∪ T2 ⊢ A[s // 0],
        fapply weakening', exact hT1, exact hT2,
      
      split, simp only [*, fol.subst_formula, list.mem_union] at *, fapply subst, exact s, exact t, exact A,
      exact this.fst, exact this.snd,
      simp only [*, fol.subst_formula, eq_self_iff_true],
      intro ψ, intro hψ,
      simp only [*, -hψ, fol.subst_formula, list.mem_union, set.mem_set_of_eq] at hψ,
      cases hψ, fapply S1.snd.snd, exact hψ, fapply S2.snd.snd, exact hψ,
    end

noncomputable def theory_proof_compactness {L : Language} {T : Theory L} {ψ : sentence L} (hψ : T ⊢ ψ) : Σ' Γ : list (sentence L), Σ' P : {ϕ : sentence L | ϕ ∈ Γ} ⊢ (ψ : sentence L), {ϕ : sentence L | ϕ ∈ Γ} ⊆ T :=
  begin
  have P := proof_compactness hψ, cases P with P hP,
  have lift_list := begin fapply @image_lift_list, exact sentence L, exact formula L, exact sigma.fst, exact T, exact P, exact hP.snd end, 
  refine ⟨lift_list.fst,_, _⟩, swap, exact lift_list.snd.left,
  change Theory.fst {ϕ : sentence L | ϕ ∈ lift_list.fst} ⊢ ψ.fst,
  unfold Theory.fst, rw[lift_list.snd.right], exact hP.fst
  end

theorem compactness {L : Language} {T : Theory L} {f : sentence L}: T ⊨ f ↔ ∃ fs : list (sentence L), {ϕ | ϕ ∈ fs} ⊨ f ∧ {ϕ | ϕ ∈ fs} ⊆ T :=
begin
  split, intro H, have : T ⊢' f, exact (completeness T f).mpr H,
  have finite_support := theory_proof_compactness (classical.choice this),
  refine ⟨finite_support.fst, _⟩, refine and.intro _ finite_support.snd.snd, fapply soundness, exact finite_support.snd.fst,
  intro H, cases H with fs hFS, fapply soundness,
  have := classical.choice ((completeness {ϕ : sentence L | ϕ ∈ fs} f).mpr hFS.left),
  fapply weakening, exact Theory.fst {ϕ : sentence L | ϕ ∈ fs}, swap, assumption,
  fapply set.image_subset, exact hFS.right,
end
