import .fol order.zorn order.filter logic.basic data.finset data.set data.list .completeness
local attribute [instance, priority 0] classical.prop_decidable
open fol set

universes u v

/-- Given an xs : list α, an x : α, a set T on α such that everything in xs which is not x is in T, return the sublist which excludes x, a proof that this list is now a subset of T, and a proof that everything in this list was not the forbidden element x. --/
def list_except {α : Type u} [decidable_eq α] (xs : list α) (x : α) (T : set α) 
  (h : ∀ y ∈ xs, y ≠ x → y ∈ T) : 
  Σ' ys : list α, ({ϕ | ϕ ∈ ys} ⊆ T ∧ (∀ y ∈ ys, y ≠ x)) ∧ (∀ y ∈ xs, y ≠ x → y ∈ ys) :=
begin
  existsi xs.filter (≠ x),
  refine ⟨⟨_, _⟩, _⟩,
  { intros y hy, apply h y (list.mem_of_mem_filter hy), apply list.of_mem_filter hy },
  { intros y hy, apply list.of_mem_filter hy },
  { intros y hy hxy, apply list.mem_filter_of_mem hy hxy }
end

open classical

/- Couldn't find this def in set.basic... sure it's around somewhere-/
/-- Given x ∈ f '' S, choose a lift x' in the preimage of x; return x' and a proof that x' is a lift --/
noncomputable def image_lift {α : Type u} {β : Type v} {f : α → β} {S : set α} (x ∈ f '' S) : Σ' (x' : α), x' ∈ S ∧ f x' = x :=
begin
  apply psigma_of_exists, apply (set.mem_image _ _ _).mp H
end

/-- Given a list xs : list β, a set S : set α, a proof that {x | x ∈ xs} ⊆ f '' S, return a list of lifts ys : list α, a proof that ys ⊆ S and a proof that f '' ys = xs --/
noncomputable def image_lift_list {α : Type u} {β : Type v} {f : α → β} {S : set α} {xs : list β} (h_sub : {x | x ∈ xs} ⊆ f '' S) : Σ' (ys : list α), ({y' | y' ∈ ys} ⊆ S) ∧ f '' {y | y ∈ ys} = {x | x ∈ xs} :=
begin
  apply psigma_of_exists, 
  rcases list.exists_of_to_set_subset_image h_sub with ⟨ys, hys, hys'⟩,
  refine ⟨ys, hys, _⟩, subst hys', ext,
  apply list.mem_map.symm
end

open finset
/-- Any proof from a set of formulas is provable from a finite subformulas. --/
lemma proof_compactness {L : Language.{u}} {ψ : formula L} {T : set $ formula L} :
  (T ⊢' ψ) → ∃Γ : finset (formula L), ↑Γ ⊢' ψ ∧ ↑Γ ⊆ T :=
begin
  intro P, induction P with P, induction P,
  { exact ⟨{P_A}, ⟨axm1⟩, set.singleton_subset_iff.mpr P_h⟩ },
  { rcases P_ih with ⟨Γ, H, K⟩, refine ⟨Γ \ {P_A}, impI' $ weakening' (by simp) H, by simp [K]⟩ },
  { rcases P_ih_h₁ with ⟨Γ₁, H₁, K₁⟩, rcases P_ih_h₂ with ⟨Γ₂, H₂, K₂⟩,
    refine ⟨Γ₁ ∪ Γ₂, impE' _ (weakening' (by simp) H₁) (weakening' (by simp) H₂), by simp [K₁, K₂]⟩ },
  { rcases P_ih with ⟨Γ, H, K⟩, refine ⟨Γ \ {∼P_A}, falsumE' $ weakening' (by simp) H, by simp [K]⟩ },
  { rcases P_ih with ⟨Γ, H, K⟩, rcases exists_of_subset_image K with ⟨Γ', K', hΓ⟩,
    subst hΓ, simp only [finset.coe_image] at H K, 
    exact ⟨Γ', allI' H, K'⟩ },
  { rcases P_ih with ⟨Γ, H, K⟩, exact ⟨Γ, allE₂' H, K⟩ },
  { exact ⟨∅, ref' _ _, empty_subset _⟩ },
  { rcases P_ih_h₁ with ⟨Γ₁, H₁, K₁⟩, rcases P_ih_h₂ with ⟨Γ₂, H₂, K₂⟩,
    refine ⟨Γ₁ ∪ Γ₂, subst₂' _ _ _ (weakening' (by simp) H₁) (weakening' (by simp) H₂), by simp [K₁, K₂]⟩ }
end


lemma theory_proof_compactness {L : Language} {T : Theory L} {ψ : sentence L} (hψ : T ⊢' ψ) : 
  ∃Γ : finset (sentence L), ↑Γ ⊢' ψ ∧ ↑Γ ⊆ T :=
begin
  rcases proof_compactness hψ with ⟨Γ, H, K⟩, 
  rcases exists_of_subset_image K with ⟨Γ', K', hΓ⟩,
  subst hΓ, simp only [finset.coe_image] at H K, 
  exact ⟨Γ', H, K'⟩
end

lemma theory_proof_compactness_iff {L : Language} {T : Theory L} {ψ : sentence L} : 
  T ⊢' ψ ↔ ∃Γ : finset (sentence L), ↑Γ ⊢' ψ ∧ ↑Γ ⊆ T :=
⟨theory_proof_compactness, λ⟨Γ, H, K⟩, weakening' (image_subset _ K) H⟩

theorem compactness {L : Language} {T : Theory L} {f : sentence L} : 
  T ⊨ f ↔ ∃ fs : finset (sentence L), ↑fs ⊨ f ∧ ↑fs ⊆ T :=
begin
  rw [←completeness T f, theory_proof_compactness_iff], simp [completeness]
end
