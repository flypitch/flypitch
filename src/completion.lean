/- Show that every theory can be extended to a complete theory -/

import .fol order.zorn order.filter logic.basic data.finset data.set tactic.tidy
local attribute [instance, priority 0] classical.prop_decidable
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

open classical
noncomputable def instantiate_existential {α : Type} {P : α → Prop} (h : ∃ x : α, P x) : nonempty α → {x // P x} :=
begin
intro h_nonempty,
let X := (@strong_indefinite_description α P h_nonempty),
refine ⟨X.val, _⟩,
apply X.property,
exact h
end

noncomputable lemma dne4 {α : Type} (h : ¬(α → false)) : α :=
begin
by_cases nonempty α,
exact classical.choice h,
dedup, have p := not.elim h_1, swap, exact false,
have f := λ x : α, p (nonempty.intro x),
contradiction
end

lemma dne5 {p q} (h : p → q) : ¬ q → ¬ p := by tauto

lemma can_extend {L : Language} (T : Theory L) (ψ : sentence L) (h : is_consistent T): (is_consistent (T ∪ {ψ})) ∨ (is_consistent (T ∪ {∼ ψ}))
:=
begin
simp[is_consistent],
by_contra,
rename a hc,
rw[not_or_distrib] at hc,
cases hc with hc1 hc2,
apply h,
have hc_uno : T ⊢  ψ ⟹ s_falsum,
  fapply simpI, fapply dne4, assumption,
  have hc_ein := @not.elim _ false hc1,
have hc_dos : T ⊢ ∼ψ ⟹ s_falsum,
  fapply simpI, fapply dne4, assumption,
  have : ψ ⟹ s_falsum = s_not ψ, by refl, rw[this] at hc_uno,
  have : (s_not ψ) ⟹ s_falsum = s_not (s_not ψ), by refl, rw[this] at hc_dos,
have hc_tres : T ⊢ (∼ ψ) ⊓ (∼ ∼ ψ),
  apply sandI hc_uno hc_dos,
exact @snot_and_self L T ∼ψ hc_tres,
end

/- Given a consistent theory T and sentence ψ, return whichever one of T ∪ ψ or T ∪ ∼ ψ is consistent.  We will need `extend` to show that the maximal theory given by Zorn's lemma is complete. -/
noncomputable def extend {L : Language} (T : Theory L) (ψ : sentence L) (h : is_consistent T) : Σ' T : Theory L, is_consistent T :=
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

def Theory_over {L : Language} (T : Theory L) (hT : is_consistent T): Type := {T' : Theory L // T ⊆ T' ∧ is_consistent T'}

/- Every theory T is trivially a theory over itself -/
def over_self {L : Language} (T : Theory L) (hT : is_consistent T): Theory_over T hT:=
  by {refine ⟨T, _⟩, split, trivial, assumption}



def Theory_over_subset {L : Language} {T : Theory L} {hT : is_consistent T} : Theory_over T hT → Theory_over T hT→ Prop
:= λ T1 T2, T1.val ⊆ T2.val

instance {T : Theory L} {hT : is_consistent T} : has_subset (Theory_over T hT) := ⟨Theory_over_subset⟩

instance {T : Theory L} {hT : is_consistent T} : nonempty (Theory_over T hT) := ⟨over_self T hT⟩

/- Given a set of theories over T and a proof that they form a chain under set-inclusion,
return their union and a proof that this contains every theory in the chain
-/

/-- Given T ⊢ ψ, return the finite context from T required to prove ψ, a proof of that, and a proof that the finite conte
xt was a subset of T --/
def finsubset {α : Type} (S : set α) := Σ' Γ : finset α, {γ | γ ∈ Γ} ⊆ S

-- def proof_formula_finite_support : ∀{L}, ∀{T : set $ formula L}, ∀{ψ : formula L}, Π proof : prf T ψ, Σ Γ : finsubset T, prf {γ | γ ∈ Γ.fst} ψ
-- | L T falsum proof := begin destruct proof, introv, intros h1 h2 h3, simp*, split, swap, split, swap, exact {falsum}, have : falsum ∈ T, rw[h1, h2], assumption, intro ele, intro h_ele, cases h_ele, finish, cases h_ele, apply exfalso, apply axm, simp, introv, intros h1 h2 h3, cases h2, introv, intros h1 h2 h3, split, swap, split, swap, exact (proof_formula_finite_support a).fst.fst ∪ (proof_formula_finite_support a_1).fst.fst, simp*, intro, intro, cases a_3,  repeat{sorry} end -- yuck

/- A simple consequence of weakening, needed for recursion below  -/
lemma weakening' {L : Language} {S_1 S_2 : set $ formula L} {ψ_1 ψ_2 : formula L} (p1 : S_1 ⊢ ψ_1) (p2 : S_2 ⊢ ψ_2) : (S_1 ∪ S_2 ⊢ ψ_1) × (S_1 ∪ S_2 ⊢ ψ_2) :=
  begin
    split, fapply @weakening L S_1 (S_1 ∪ S_2), simpa,
    fapply @weakening L S_2 (S_1 ∪ S_2), simpa,
  end

/- Given an xs : list α, an x : α, a set T on α such that everything in xs which is not x is in T, return the sublist which excludes x, a proof that this list is now a subset of T, and a proof that everything in this list was not the forbidden element x.

Annoyingly, I seem to need this to handle impI case below.
-/

noncomputable def list_except {α : Type} (xs : list α) (x : α) (T : set α) (h : ∀ y ∈ xs, y ≠ x → y ∈ T) : Σ' ys : list α, ({ϕ | ϕ ∈ ys} ⊆ T ∧ (∀ y ∈ ys, y ≠ x)) ∧ (∀ y ∈ xs, y ≠ x → y ∈ ys) :=
begin
  induction xs generalizing h,
    split, swap, exact list.nil, simp,
    split, swap, refine if _ then _ else _,
    {exact xs_hd = x,},
    {apply_instance,},
    {refine (xs_ih _).fst, intros, fapply h, simp, exact or.inr H, assumption},
    {refine _::((xs_ih _).fst), exact xs_hd, intros, fapply h, simp, exact or.inr H, assumption},  -- finish ite statement
  split, split,
  
  by_cases xs_hd = x; simp*; intros a ha; simp[*, -ha] at ha,
     {dedup, refine (xs_ih _).snd.left.left _, intros, fapply h, simp, exact or.inr H, assumption, assumption,},
     {dedup, cases ha, swap,
     refine (xs_ih _).snd.left.left _, intros, fapply h, simp, exact or.inr H, assumption, assumption, fapply h, fapply or.inl, assumption, cc},

    by_cases (xs_hd = x);
      simp*, intros y H, refine ((xs_ih _).snd).left.right _ _,
      intros, dedup, fapply h, simp, apply or.inr, assumption,
      assumption, assumption,
      
      intros y H, refine ((xs_ih _).snd).left.right _ _,
      intros, dedup, fapply h, simp, apply or.inr, assumption,
      assumption, assumption, 

    intro y, intro hy, by_cases xs_hd = x, simp*, 
    cases hy, intro h_bad, have : y = x, by cc, contradiction,
      
         begin
         intro h_good, fapply (xs_ih _).snd.right y,
           exact hy, exact h_good, 
         end,
             
         begin
         intro h_good, simp*, cases hy, exact or.inl hy, fapply or.inr, fapply (xs_ih _).snd.right y,
           exact hy, exact h_good,
         end,
end

/- Couldn't find this def in set.basic... sure it's around somewhere-/
/-- Given x ∈ f '' S, choose a lift x' in the preimage of x; return x' and a proof that x' is a lift --/
noncomputable def image_lift {α β : Type} {f : α → β} {S : set α} (x ∈ f '' S) : Σ' (x' : α), x' ∈ S ∧ f x' = x :=
begin
  simp[*,-H] at H,
  have := strong_indefinite_description, swap, exact α,
  have prelift : {x_1 // (∃ (y : α), (λ (y : α), y ∈ S ∧ f y = x) y) → (λ (y : α), y ∈ S ∧ f y = x) x_1},
  fapply this (λ y, y ∈ S ∧ f y = x), fapply nonempty_of_exists, exact (λ y, y ∈ S ∧ f y = x),
  exact H, have snd := prelift.property, simp[*,-snd] at snd,
  refine ⟨prelift.val, _⟩, exact snd,
end

/-- Given a list xs : list β, a set S : set α, a proof that {x | x ∈ xs} ⊆ f '' S, return a list of lifts ys : list α, a proof that ys ⊆ S and a proof that f '' ys = xs --/
noncomputable def image_lift_list {α β : Type} {f : α → β} {S : set α} {xs : list β} (h_sub : {x | x ∈ xs} ⊆ f '' S) : Σ' (ys : list α), ({y' | y' ∈ ys} ⊆ S) ∧ f '' {y | y ∈ ys} = {x | x ∈ xs} :=
begin
  induction xs generalizing h_sub,
    split, swap,
      {exact list.nil},
      {fapply and.intro, repeat{simp}},
  
          let Hxs_ih : {x : β | x ∈ xs_tl} ⊆ f '' S :=
            begin intros x hx, fapply h_sub, exact or.inr hx end,
          let Himage_lift : xs_hd ∈ (f '' S) :=
            begin fapply h_sub, simp end, simp[*, -Himage_lift] at Himage_lift,
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

        simp*, fapply funext, intro x, fapply propext,

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

noncomputable def proof_compactness {L : Language} : Π {ψ : formula L}, Π {T : set $ formula L},  Π (pψ : T ⊢ ψ), Σ Γ : list (formula L), Σ' p : {ϕ : formula L | ϕ ∈ Γ} ⊢ ψ, {ϕ : formula L | ϕ ∈ Γ} ⊆ T
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
      
      split, simp* at this, simp*,fapply impE, exact A,
      exact this.fst, exact this.snd, simp*, intro ψ, intro hψ,
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
        exact or.inl h, simp*, fapply hS'.right, assumption, assumption},
    
    {fapply weakening, exact {ϕ : formula L | ϕ ∈ S.fst}, exact h_weakening, exact S.snd.fst}
  end
| A T (falseE P) :=
  begin
    have S := (proof_compactness P),
    let S' := --Σ' (ys : list (formula L)), {ϕ : formula L | ϕ ∈ ys} ⊆ T ∧ ∀ (y : formula L), y ∈ ys → y ≠ f1,
      begin { refine (list_except S.fst (∼A) T _),
      have := (S.snd).snd, intros y H a, have := this H, cases this, exfalso, contradiction, assumption}, end,
    split, swap,  exact S'.fst, have hS' := S'.snd, 
    split, swap, exact hS'.left.left,
    fapply falseE,
    have h_weakening : {ϕ : formula L | ϕ ∈ S.fst} ⊆ insert ∼A {ϕ : formula L | ϕ ∈ S'.fst},
      {intro x, intro hx, simp, by_cases x = ∼A,
        exact or.inl h, simp*, fapply hS'.right, assumption, assumption},
 
    {fapply weakening, exact {ϕ : formula L | ϕ ∈ S.fst}, exact h_weakening, exact S.snd.fst}  
  end
|  (∀' A) T (allI P) :=
  begin
    have S  := (proof_compactness P), have h_subset := S.snd.snd,
    have preS' := image_lift_list h_subset, let S' := preS'.fst, have hS' := preS'.snd,
    refine ⟨S', _⟩, refine ⟨_, hS'.left⟩, fapply allI,
    rw[hS'.right], exact S.snd.fst,
  end
| (_ ≃ t) T (refl _ _) :=
  begin
    dedup, refine ⟨[], _⟩, split, fapply fol.prf.refl,
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
      
      split, simp* at this, simp*,fapply subst, exact s, exact t, exact A,
      exact this.fst, exact this.snd, simp*, intro ψ, intro hψ, simp[*,-hψ] at hψ,
      cases hψ, fapply S1.snd.snd, exact hψ, fapply S2.snd.snd, exact hψ,
    end

-- def proof_finite_support2 {L : Language} (T : Theory L) (ψ : sentence L) (pψ : T ⊢ ψ) : Σ Γ : list (sentence L), Σ' p :{ϕ : sentence L | ϕ ∈ Γ} ⊢ ψ, {ϕ : sentence L | ϕ ∈ Γ} ⊆ T :=
-- begin
--   split, swap,
--   unfold sprf at pψ, have ψ_1 := ψ.fst, have ψ_2 := ψ.snd, induction pψ generalizing ψ,
--   {exact [ψ],},
--   {sorry},
--   {sorry},
--   {sorry},
--   {sorry},
--   {sorry},
--   {sorry},
--   {sorry},
--   {sorry}
-- end

/- Given a sentence and the knowledge that there is a proof of ψ from T, return a list of sentences from T and a proof that this list proves ψ -/
noncomputable def proof_finite_support {L : Language} (T : Theory L) (ψ : sentence L) (hψ : T ⊢' ψ) : Σ' Γ : list (sentence L), {ϕ : sentence L | ϕ ∈ Γ} ⊢' ψ ∧ {ϕ : sentence L | ϕ ∈ Γ} ⊆ T :=
begin
  have P := classical.choice hψ,
  have P' := proof_compactness P,
  cases P' with S hS,
  have lift_list := begin fapply @image_lift_list, exact sentence L, exact formula L, exact sigma.fst, exact T, exact S, exact hS.snd end,
  refine ⟨lift_list.fst, _⟩,
  refine and.intro _ lift_list.snd.left, fapply nonempty.intro,
  unfold Theory.fst, rw[lift_list.snd.right], exact hS.fst
end

lemma in_theory_of_fst_in_theory {L : Language} {T : Theory L} {ψ : sentence L} (h : ψ.fst ∈ T.fst) : ψ ∈ T :=
begin
cases ψ,
  unfold Theory.fst at h, unfold set.image at h,
  have lift : ∃ (a : Σ (f : formula L), formula_below 0 f), a ∈ T ∧ a.fst = ψ_fst,
  assumption,
  cases lift with lift1 lift2,
  cases lift2 with lift2 hlift2,
  cases lift1 with lift1 hlift1,
  have : sigma.mk lift1 hlift1 = ⟨ψ_fst, ψ_snd⟩,
  simp*, split, assumption, finish,
  rw[this] at lift2, assumption
end
-- def provable_of_provable_from_subset2 : ∀{L}, Π ψ : sentence L, Π(T : Theory L), Π(T' : Theory L), T' ⊆ T → T' ⊢ ψ  → T ⊢ ψ
-- | L ψ T T' h_sub (axm a) := begin --fapply axm, unfold has_subset.subset at h_sub, fapply set.image_subset, exact T', exact h_sub, exact a end
-- sorry end


--  fapply axm, exact h_sub a 


def provable_of_provable_from_subset {L : Language} (T : Theory L) (T' : Theory L) (h_sub : T' ⊆ T) (ψ : sentence L) (proof : T' ⊢ ψ) : (T ⊢ ψ)
 :=
begin
fapply weakening,
exact T'.fst, fapply set.image_subset, assumption,
assumption
end

/- Given a chain of sets with nonempty union, conclude that the chain is nonempty-/
def nonempty_chain_of_nonempty_union {α : Type} {A_i : set $ set α} {h_chain : chain set.subset A_i} (h : nonempty $ set.sUnion A_i) : nonempty A_i :=
begin
have a := classical.choice h,
cases a with a_val a_property, unfold set.sUnion at a_property, simp at a_property,
cases a_property with A hA, simp, fapply exists.intro, exact A, exact hA.left
end

/- Given a chain on α over a fixed T and a list of elements of the union over T, return a set which contains all elements of the list, and, if the list is nonempty, a proof that this set was in the chain -/
def sup_list {α : Type} (T : set α) (A_i : set $ set α) (h_chain : chain set.subset A_i) (as : list α)
(h_as : ∀ a ∈ as, a ∈ T ∪ set.sUnion A_i) : Σ' A_n : set α, ∀ a ∈ as, a ∈ A_n  → A_n ∈ insert T A_i :=
begin
induction as, split, swap, exact T,
simp*,
split, swap,

--  have h_nonempty : nonempty A_i, fapply nonempty_chain_of_nonempty_union, assumption, apply nonempty.intro, 
end

def sup_list2 {α : Type} (T : set α) (A_i : set $ set α) (h_chain : chain set.subset A_i) (h_over_T : ∀ A ∈ A_i, T ⊆ A) (as : list α) (h_as : ∀ a ∈ as, a ∈ T ∪ set.sUnion A_i) : Σ' A_n : set α, ∀ a ∈ as, a ∈ A_n → nonempty A_n → A_n ∈ A_i :=
begin
induction as with as ih,
  simp*, exact ⟨T, trivial⟩,
  
end

/- Given two elements in a chain of sets over T, their union over T is in the chain -/
lemma in_chain_of_union {α : Type} (T : set α) (A_i : set $ set α) (h_chain : chain set.subset A_i) (as : list A_i) (h_over_T : ∀ A ∈ A_i, T ⊆ A) (A1 A2 ∈ A_i) : A1 ∪ A2 = A1 ∨ A1 ∪ A2 = A2 :=
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

def image_list {α β : Type} (f : α → β) (xs : list α) : list β :=
  begin
    induction xs,
    exact list.nil,
    exact (f xs_hd) :: xs_ih
  end

/- Given a list of elements in a chain of sets over T, their union over T is in the chain -/
lemma in_chain_of_finite_union
{α : Type}
(T : set α)
(A_i : set $ set α)
(h_chain : chain set.subset A_i)
(as : Σ' (xs : list $ set α), ∀ a ∈ xs, (A_i a)) :
--(as : list $ Σ' ( A : set α), A_i A) :
  begin
    refine _ ∈ insert T A_i,
    fapply @list.foldr (set α) (set α),
    exact λ a b, set.union T $ set.union a b, exact T, fapply image_list, exact Σ' ( A : set α), A_i A,
    intro pair, cases pair, exact pair_fst, 

  {
    cases as, induction as_fst,
    exact list.nil, have h_hd := as_snd as_fst_hd begin simp* end, have p_hd := psigma.mk as_fst_hd h_hd, apply list.cons, exact p_hd, have : (∀ (a : set α), a ∈ as_fst_tl → A_i a), intro a, intro ha,
    have h2 := as_snd a, simp at h2, have : a = as_fst_hd ∨ a ∈ as_fst_tl, apply or.inr, exact ha, exact h2 this, exact as_fst_ih this
}
 end :=
  begin
simp*,
    -- induction as, tidy, unfold image_list, simp,
    -- unfold set.union list.foldr, 
  end
 -- A_i (@set.Union α {a // a ∈ as} (begin intro, cases a, exact a_val.fst end)) :=
-- begin
-- induction as,
--   simp*, 
-- end

/- the image of a chain of Theory_over T's under subtype.val is a chain -/
lemma val_chain {L : Language} {T : Theory L} {hT : is_consistent T} (Ts : set (Theory_over T hT)) (h_chain : chain Theory_over_subset Ts) : chain set.subset (subtype.val '' Ts) :=
begin
repeat{sorry},
-- simp[Theory_over_subset] at h_chain, 
    -- simp[*, chain, set.pairwise_on, -h_chain] at h_chain,
    -- intros T1  hT1  T2  hT2  H,
    -- unfold set.image at hT1 hT2,
    -- simp[*, -hT2, -hT1]  at hT2 hT1,
    -- apply classical.choice, apply nonempty_of_exists,
end


lemma finite_sup : Π(L : Language), Π(T : Theory L), Π(hT : is_consistent T), Π(Ts : set (Theory_over T hT)), Π(h_chain : chain Theory_over_subset Ts),
Π(h_inconsis : T ∪ ⋃₀(subtype.val '' Ts) ⊢' s_falsum),
(sup_list T (subtype.val '' Ts) _ ((proof_finite_support (T ∪ ⋃₀(subtype.val '' Ts)) ⊥ h_inconsis).fst) _).fst ∈ subtype.val '' Ts ∧
    {ψ : sentence L | ψ ∈ (proof_finite_support (T ∪ ⋃₀(subtype.val '' Ts)) ⊥ h_inconsis).fst} ⊆ (sup_list T (subtype.val '' Ts) _ ((proof_finite_support (T ∪ ⋃₀(subtype.val '' Ts)) ⊥ h_inconsis).fst) _).fst := sorry

/--Given a chain and two elements from this chain, return their maximum. --/
noncomputable def max_in_chain {α : Type} {R : α → α → Prop} {Ts : set α} {nonempty_Ts : nonempty Ts} (h_chain : chain R Ts) (S1 S2 : α) (h_S1 : S1 ∈ Ts) (h_S2 : S2 ∈ Ts) : Σ' (S : α), (S = S1 ∧ (R S2 S1 ∨ S1 = S2)) ∨ (S = S2 ∧ (R S1 S2 ∨ S1 = S2)) :=
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
noncomputable def max_of_list_in_chain {α : Type} {R : α → α → Prop} {trans : ∀{a b c}, R a b → R b c → R a c} {Ts : set α} {nonempty_Ts : nonempty Ts} (h_chain : chain R Ts) (Ss : list α) -- {nonempty_Ss : nonempty {S | S ∈ Ss}}
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

noncomputable def finite_sup_T_lemma_1 {L : Language} {T : Theory L} {hT : is_consistent T} (Ts : set (Theory_over T hT)) (hTs : nonempty Ts) (h_chain : chain Theory_over_subset Ts) (h_inconsis : T ∪ ⋃₀(subtype.val '' Ts) ⊢' (⊥ : sentence L)) (fs : list (sentence L)) (Hfs : {ϕ : sentence L | ϕ ∈ fs} ⊢' (⊥ : sentence L) ∧ {ϕ : sentence L | ϕ ∈ fs} ⊆ T ∪ ⋃₀(subtype.val '' Ts)) : Π (f : sentence L), f ∈ fs → (Σ' (S_f : Theory_over T hT), set.mem S_f Ts ∧ set.mem f (S_f.val)) :=
begin
  intros f hf,
  have H := Hfs.right,
  unfold set.image set.sUnion set.subset set.mem list.mem at H,
  have H' := H hf,
  by_cases f ∈ T,
  split, swap,
  {exact (classical.choice hTs).val},
  {fapply and.intro, exact (choice hTs).property,
    have H := (choice hTs).val.property.left,
    exact H h},
 

    simp[*, -H'] at H',
    have witness := instantiate_existential H' begin fapply nonempty.intro, exact T end, simp* at witness,
    split, swap, split, swap, exact witness.val, cases witness.property with case1 case2, cases case1 with case1' case1'', exact case1',

split, have witness_property := witness.property, cases witness_property with case1 case2, cases case1 with case1' case1'', exact case1'',

have witness_property := witness.property, cases witness_property with case1 case2,
exact case2,
end

@[reducible]def list_is_list_of_subtype (L : Language) (fs : list (sentence L)) -- (Hfs : {ϕ : sentence L | ϕ ∈ fs} ⊢' (⊥ : sentence L) ∧ {ϕ : sentence L | ϕ ∈ fs} ⊆ T ∪ ⋃₀(subtype.val '' Ts))
-- (dSs : Π (f : sentence L), f ∈ fs → (Σ' (S_f : Theory_over T hT), set.mem S_f Ts ∧ set.mem f (S_f.val)))
: list ↥{f : sentence L | f ∈ fs} :=
begin
  induction fs,
  exact [],

  refine _::_,
  split, swap, exact fs_hd, simp,
  have : {f | f ∈ fs_tl} → {f | f ∈ list.cons fs_hd fs_tl},
  intro f, split, swap, exact f.val, exact or.inr f.property,
  fapply list.map this, exact fs_ih
end

noncomputable def finite_sup_T_lemma_2 {L : Language} (T : Theory L) (hT : is_consistent T) (Ts : set (Theory_over T hT)) (hTs : nonempty Ts) (h_chain : chain Theory_over_subset Ts) (h_inconsis : T ∪ ⋃₀(subtype.val '' Ts) ⊢' (⊥ : sentence L)) (fs : list (sentence L)) (Hfs : {ϕ : sentence L | ϕ ∈ fs} ⊢' (⊥ : sentence L) ∧ {ϕ : sentence L | ϕ ∈ fs} ⊆ T ∪ ⋃₀(subtype.val '' Ts)) (dSs : Π (f : sentence L), f ∈ fs → (Σ' (S_f : Theory_over T hT), set.mem S_f Ts ∧ set.mem f (S_f.val))) :  Σ' (T_max : Theory_over T hT), T_max ∈ Ts ∧ ∀ (ψ : sentence L), ψ ∈ fs → ψ ∈ T_max.val :=
begin
  let F : {f | f ∈ fs} → Theory_over T hT :=
    begin intro f, exact (dSs f.val f.property).fst end,
 let fs_list_subtype := list_is_list_of_subtype L fs,
 let T_list : list (Theory_over T hT) :=
    begin fapply list.map F, exact fs_list_subtype end,
  have T_list_subset_Ts : (∀ (S : Theory_over T hT), S ∈ T_list → S ∈ Ts),
    intro S, simp, intros x h1 h2, simp[*,-h2] at h2, rw[<-h2.right],
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
            refine this _, simp*, fapply exists.intro, exact f, fapply exists.intro,
            exact hf, fapply and.intro, unfold has_mem.mem list.mem,
            {sorry},
            {refl},
            end,
        cases so_close with case1 case2,
        rw[case1], intros a h, exact h,
        exact case2,
        exact nearly_there almost_there,
        },
      },
    {intros a b c, unfold Theory_over_subset, fapply subset_is_transitive},
    {assumption},
end

/--Given a consistent theory T and a chain Ts of consistent theories over T, and a finite list of formulas in ⋃Ts which prove ⊥, return the assertion that there exists a theory T' from Ts ∪ {T} and a proof that T' ⊢ ⊥. (This probably should be refactored through nonempty.intro) --/
def finite_sup_T  {L : Language} {T : Theory L}  {hT : is_consistent T} {Ts : set (Theory_over T hT)} {hTs : nonempty Ts} {h_chain : chain Theory_over_subset Ts} {h_inconsis: T ∪ ⋃₀(subtype.val '' Ts) ⊢' s_falsum} (Γpair : Σ' (Γ : list (sentence L)),
    {ϕ : sentence L | ϕ ∈ Γ} ⊢' (⊥ : sentence L) ∧ {ϕ : sentence L | ϕ ∈ Γ} ⊆ T ∪ ⋃₀(subtype.val '' Ts)) : ∃ (T' : Theory L), T' ∈ subtype.val '' Ts ∧ {ψ : sentence L | ψ ∈ Γpair.fst} ⊆ T' :=
begin
  cases Γpair with fs Hfs, 
  have dSs : Π f ∈ fs, Σ' S_f : (Theory_over T hT), set.mem S_f Ts ∧ (set.mem (f) (S_f.val)), -- to each f in fs, associate an S_f containing f from the chain
    {fapply finite_sup_T_lemma_1, repeat{assumption}},
  have T_max : Σ' (T_max : Theory_over T hT), (T_max ∈ Ts) ∧ ∀ ψ ∈ fs, (ψ) ∈ T_max.val,  -- get the theory and a proof that it contains all the f
    {fapply finite_sup_T_lemma_2, repeat{assumption}},
  
  fapply exists.intro, exact T_max.fst.val,
  fapply and.intro, fapply set.mem_image_of_mem, exact T_max.snd.left,
  have := T_max.snd.right, intros ψ hψ, exact this ψ hψ,
end

-- example : ∀{L}, ((∅ : Theory L) ⊢ s_falsum → false) :=
--   begin
--     intros L P, unfold sprf at P, destruct P,
--   end 

/- The limit theory of a chain of consistent theories over T is consistent -/
lemma consis_limit {L : Language} {T : Theory L} {hT : is_consistent T} (Ts : set (Theory_over T hT)) (h_chain : chain Theory_over_subset Ts) : is_consistent (T ∪ set.sUnion (subtype.val '' Ts)) :=
begin -- so _here_ is where we need that proofs are finitely supported
  apply is_consistent_intro, intro h_inconsis,
  by_cases nonempty Ts, swap,
    { simp* at h, simp[*, -h_inconsis] at h_inconsis, unfold is_consistent at hT, exact hT (classical.choice h_inconsis)},

  have Γpair := proof_finite_support (T ∪ ⋃₀(subtype.val '' Ts)) ⊥ h_inconsis,
  have h_bad : ∃ T' : (Theory L), (T' ∈ (subtype.val '' Ts)) ∧ {ψ | ψ ∈ Γpair.fst} ⊆ T',

  fapply finite_sup_T, repeat{assumption},

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

    induction T_bad_inconsis, exact T_bad_consis T_bad_inconsis, 
end

--refine @exists.elim ( T ⊆ T_bad.val ∧ is_consistent (T_bad.val)) (λ x :  T ⊆ T_bad.val ∧ is_consistent (T_bad.val), ⟨_, x⟩ ∈ Ts), swap},



/-- Given a chain of consistent extensions of a theory T, return the union of those theories and a proof that this is a consistent extension of T --/

def limit_theory2 {L : Language} {T : Theory L} {hT : is_consistent T} (Ts : set (Theory_over T hT)) (h_chain : chain Theory_over_subset Ts) : Σ' T : Theory_over T hT, ∀ T' ∈ Ts, T' ⊆ T :=
begin
refine ⟨⟨T ∪ set.sUnion (subtype.val '' Ts), _⟩, _⟩, simp*, intro,
exact @consis_limit L T hT Ts h_chain begin simpa* end,
intros T' hT' ψ hψ, right, split, swap, exact T'.val,
apply exists.intro, swap, exact hψ, simp*, exact T'.property
end

/- Given a theory T, show that the poset of theories over T satisfies the hypotheses of Zorn's lemma -/
lemma can_use_zorn2 {L : Language} {T : Theory L} {hT : is_consistent T}  : (∀c, @chain (Theory_over T hT) Theory_over_subset c → ∃ub, ∀a∈c, a ⊆ ub) ∧ (∀(a b c : Theory_over T hT), a ⊆ b → b ⊆ c → a ⊆ c) :=
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


/- Given a consistent theory T, return a maximal extension of it given by Zorn's lemma, along with the proof that it is consistent and maximal -/
noncomputable def maximal_extension2 (L : Language) (T : Theory L) (hT : is_consistent T)  : Σ' (T_max : Theory_over T hT), ∀ T' : Theory_over T hT, T_max ⊆ T' → T' ⊆ T_max :=
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

lemma cannot_extend_maximal_extension2 {L : Language} {T : Theory L} {hT : is_consistent T} (T_max' : Σ' (T_max : Theory_over T hT), ∀ T' : Theory_over T hT, T_max ⊆ T' → T' ⊆ T_max) (ψ : sentence L) (H : is_consistent (T_max'.fst.val ∪ {ψ}))(H1 : ψ ∉ T_max'.fst.val) : false :=
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
lemma complete_maximal_extension2_of_consis {L : Language} {T : Theory L} {hT : is_consistent T}: @is_complete L (@maximal_extension2 L T hT).fst.val :=
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
noncomputable def completion_theory3 : Π ( T : Theory L) (h_consis : is_consistent T), Σ' T' : (Theory_over T h_consis), is_complete T'.val :=
begin
  intro T,
  intro h_consis,
  let T_max := maximal_extension2 L T h_consis,
  refine ⟨T_max.fst, _⟩,
  apply complete_maximal_extension2_of_consis
end

end
