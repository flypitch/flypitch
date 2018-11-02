/- Show that every theory can be extended to a complete theory -/

import .fol order.zorn order.filter logic.basic data.finset data.set tactic.tidy
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

We need an extra case to handle the case where the chain is empty. This is the third argument, which will be the default return value.
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

/- Given an xs : list α, an x : α, a set T on α such that everything in xs which is not x is in T, return the sublist which excludes x and a proof that this list is now a subset of T.

Annoyingly, I seem to need this to handle impI case below.
-/

noncomputable def list_except {α : Type} (xs : list α) (x : α) (T : set α) (h : ∀ y ∈ xs, y ≠ x → y ∈ T) : Σ' ys : list α, {ϕ | ϕ ∈ ys} ⊆ T ∧ (∀ y ∈ ys, y ≠ x) :=
begin
  induction xs generalizing h,
    split, swap, exact list.nil, simp,
    split, swap, refine if _ then _ else _,
    {exact xs_hd = x,},
    {apply_instance,},
    {refine (xs_ih _).fst, intros, fapply h, simp, exact or.inr H, assumption},
    {refine _::((xs_ih _).fst), exact xs_hd, intros, fapply h, simp, exact or.inr H, assumption},
  split, -- finish ite statement
  
  by_cases xs_hd = x; simp*; intros a ha; simp[*, -ha] at ha,
     {dedup, refine (xs_ih _).snd.left _, intros, fapply h, simp, exact or.inr H, assumption, assumption,},
     {dedup, cases ha, swap,
     refine (xs_ih _).snd.left _, intros, fapply h, simp, exact or.inr H, assumption, assumption, fapply h, fapply or.inl, assumption, cc},

    by_cases (xs_hd = x);
      simp*, intros y H, refine ((xs_ih _).snd).right _ _,
      intros, dedup, fapply h, simp, apply or.inr, assumption,
      assumption, assumption,
      
      intros y H, refine ((xs_ih _).snd).right _ _,
      intros, dedup, fapply h, simp, apply or.inr, assumption,
      assumption, assumption
end

-- lemma list_except_either_or {α : Type} (xs : list α) (x : α) (T : set α) (h1 : ∀ y ∈ xs, y ≠ x → y ∈ T) (y : α) (h2 : y ∈ xs) : y ≠ x → y ∈ (list_except xs x T h1).fst :=
-- begin
--   sorry
-- end

def proof_finite_support3 : Π{L : Language}, Π {ψ : formula L}, Π {T : set $ formula L},  Π (pψ : T ⊢ ψ), Σ Γ : list (formula L), Σ' p : {ϕ : formula L | ϕ ∈ Γ} ⊢ ψ, {ϕ : formula L | ϕ ∈ Γ} ⊆ T
| L ψ T (axm a) := begin split, swap, exact [ψ],have : {ϕ : formula L | ϕ ∈ [ψ]} = {ψ},
                   by refl, split, rw[this],
                   fapply axm, simp, rw[this], simp, exact a
                   end
| L (f1 ⟹ f2) T (impI P) :=
  begin
    have S := (proof_finite_support3 P),
    let S' := --Σ' (ys : list (formula L)), {ϕ : formula L | ϕ ∈ ys} ⊆ T ∧ ∀ (y : formula L), y ∈ ys → y ≠ f1,
      begin { refine (list_except S.fst f1 T _),
      have := (S.snd).snd, intros y H a, have := this H, cases this, exfalso, contradiction, assumption}, end,
    split, swap,  exact S'.fst, have hS' := S'.snd, 
    split, swap, exact hS'.left,
    fapply impI,
    have : {ϕ : formula L | ϕ ∈ S.fst} ⊆ insert f1 {ϕ : formula L | ϕ ∈ S'.fst},
      intro x, intro hx, simp,
      by_cases x = f1, exact or.inl h,
      fapply or.inr, simp* at S', simp* at hS', have := hS' x, tidy, simp*, unfold list_except, 
        
      
--      by_contra, simp[not_or_distrib] at a,
      -- have := a.right,
      -- have almost_there := ((hS').right x),
      -- rename almost_there a2,
      --   have : ¬ x ∈ S'.fst → x = f1, have := dne5 a2,
      --   simp[ne] at this, assumption,
      --   dedup, have := this_1 this, contradiction,
    
    {fapply weakening, exact {ϕ : formula L | ϕ ∈ S.fst}, assumption, exact S.snd.fst}
  end
| _ _ _ (impE _ _ _) := sorry
| _ _ _ (falseE _) := sorry
| _ _ (∀' _) (allI _) := sorry
| _ _ (_ ≃ _) (refl _ _) := sorry
| _ _ .(_[_ // 0]) (allE' _ _ _) := sorry
| _ _ .(_[_ // 0]) (subst' _ _ _ _ _) := sorry

def proof_finite_support2 {L : Language} (T : Theory L) (ψ : sentence L) (pψ : T ⊢ ψ) : Σ Γ : list (sentence L), Σ' p :{ϕ : sentence L | ϕ ∈ Γ} ⊢ ψ, {ϕ : sentence L | ϕ ∈ Γ} ⊆ T :=
begin
  split, swap,
  unfold sprf at pψ, have ψ_1 := ψ.fst, have ψ_2 := ψ.snd, induction pψ generalizing ψ,
  {exact [ψ],},
  {sorry},
  {sorry},
  {sorry},
  {sorry},
  {sorry},
  {sorry},
  {sorry},
  {sorry}
end

/- Given a sentence and the knowledge that there is a proof of ψ from T, return a list of sentences from T and a proof that this list proves ψ -/
def proof_finite_support {L : Language} (T : Theory L) (ψ : sentence L) (hψ : T ⊢' ψ) : Σ' Γ : list (sentence L), {ϕ : sentence L | ϕ ∈ Γ} ⊢' ψ ∧ {ϕ : sentence L | ϕ ∈ Γ} ⊆ T:=
begin
  repeat{sorry},   
  -- rw[sprovable] at hψ,
  -- simp[sentence] at ψ,
  -- fapply psigma.mk,
  -- cases ψ,
  -- simp[sentence.fst] at hψ,
  -- cases ψ_fst,
  -- exact (list.nil).to_finset,
  -- repeat {constructor},
  -- swap, exact {}, simp,
  -- swap, exact {}, simp,
  -- swap, 

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
 unfold image_list, tidy, repeat{sorry}
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


def finite_sup_T  {L : Language} {T : Theory L}  {hT : is_consistent T} {Ts : set (Theory_over T hT)} {h_chain : chain Theory_over_subset Ts} {h_inconsis: T ∪ ⋃₀(subtype.val '' Ts) ⊢' s_falsum} (Γpair : Σ' (Γ : list (sentence L)),
    {ϕ : sentence L | ϕ ∈ Γ} ⊢' (⊥ : sentence L) ∧ {ϕ : sentence L | ϕ ∈ Γ} ⊆ T ∪ ⋃₀(subtype.val '' Ts)) : ∃ (T' : Theory L), T' ∈ subtype.val '' Ts ∧ {ψ : sentence L | ψ ∈ Γpair.fst} ⊆ T' :=
begin
fapply exists.intro, repeat{sorry} -- now we need to define a function which, given a list of sentences in the union, picks out a theory containing each member, and then takes their union (and then relativize this to over T)
end

-- example : ∀{L}, ((∅ : Theory L) ⊢ s_falsum → false) :=
--   begin
--     intros L P, unfold sprf at P, destruct P,
--   end 

/- The limit theory of a chain of consistent theories over T is consistent -/
lemma consis_limit {L : Language} {T : Theory L} {hT : is_consistent T} (Ts : set (Theory_over T hT)) (h_chain : chain Theory_over_subset Ts) : is_consistent (T ∪ set.sUnion (subtype.val '' Ts)) :=
begin -- so _here_ is where we need that proofs are finitely supported
  apply is_consistent_intro, intro h_inconsis,
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
