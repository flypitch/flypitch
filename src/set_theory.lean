/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
import .to_mathlib

/-
note: in comment above cofinality, change sentence with
+  `∀ a, ∃ b ∈ S, ¬(b > a)`. It is defined for all ordinals, but
-/

universe variables u v w w'
noncomputable theory

open ordinal set

section delta_system
variables {ι : Type w} {ι' : Type w'} {α : Type u} {β : Type v} {A : ι → set α}
def is_delta_system (A : ι → set α) :=
∃(root : set α), ∀{{x y}}, x ≠ y → A x ∩ A y = root

open cardinal
def root_subset (hι : 2 ≤ mk ι) {root : set α} (x : ι)
  (h : ∀{{x y}}, x ≠ y → A x ∩ A y = root) : root ⊆ A x :=
begin
  cases (two_le_iff' x).mp hι with y hy, rw [←h hy], apply inter_subset_left
end

def finite_root (hι : 2 ≤ mk ι) {root : set α} (h2A : ∀(x : ι), finite (A x))
  (h : ∀{{x y}}, x ≠ y → A x ∩ A y = root) : finite root :=
begin
  rcases two_le_iff.mp hι with ⟨t, u, htu⟩,
  rw [←h htu], exact finite_subset (h2A t) (inter_subset_left _ _)
end

open function
lemma is_delta_system_preimage (f : β → α) (h : is_delta_system A) :
  is_delta_system (preimage f ∘ A) :=
begin
  cases h with r hr, use f ⁻¹' r, rintro x y hxy,
  rw [←preimage_inter], apply congr_arg (preimage f), apply hr hxy
end

lemma is_delta_system_image {f : α → β} (hf : injective f) :
  is_delta_system (image f ∘ A) ↔ is_delta_system A :=
begin
  split,
  { intro h, have := is_delta_system_preimage f h,
    convert this, apply funext, intro x, dsimp, rw [preimage_image_eq _ hf] },
  rintro ⟨r, hr⟩, use f '' r, rintro x y hxy,
  rw [image_inter hf], apply congr_arg (image f), apply hr hxy
end

lemma is_delta_system_preimage_iff {f : β → α} (hf : injective f) (hf₂ : ∀i, A i ⊆ range f) :
  is_delta_system (preimage f ∘ A) ↔ is_delta_system A :=
begin
  split, rintro ⟨r, hr⟩, use f '' r, intros i j hij,
  rw [←hr hij, ←image_inter hf, image_preimage_eq_of_subset (hf₂ i),
    image_preimage_eq_of_subset (hf₂ j)],
  apply is_delta_system_preimage
end

lemma is_delta_system_precompose (f : ι' → ι) (hf : injective f) (h : is_delta_system A) :
  is_delta_system (A ∘ f) :=
by { cases h with r hr, use r, intros x y hxy, exact hr (λ hxy', hxy $ hf hxy') }

lemma is_delta_system_precompose_iff (f : ι' ≃ ι) : is_delta_system A ↔ is_delta_system (A ∘ f) :=
begin
  use is_delta_system_precompose f f.bijective.1,
  intro h, convert is_delta_system_precompose f.symm f.symm.bijective.1 h, apply funext,
  intro i, simp
end

end delta_system


namespace subrel

-- instance subrel.is_well_order' {α : Type u} (r : α → α → Prop) [is_well_order α r]
--   (p : α → Prop) : is_well_order {x // p x} (subrel r p) :=
-- subrel.is_well_order r p

end subrel

namespace delta_system

open cardinal ordinal set

open function
lemma delta_system_lemma_2 {κ : cardinal} (hκ : cardinal.omega ≤ κ)
  {θ : Type u} (θr : θ → θ → Prop) [θwo : is_well_order θ θr] (hκθ : κ < mk θ)
  (hθ : is_regular $ mk θ) (θtype_eq : ord (mk θ) = type θr) (hθ_le : ∀(β < mk θ), β ^< κ < mk θ)
  {ρ : Type u} (ρr : ρ → ρ → Prop) [ρwo : is_well_order ρ ρr] (hρ : mk ρ < κ)
  {ι : Type u} {A : ι → set θ} (h2A : ∀i, ρr ≃o subrel θr (A i))
  (h3A : unbounded θr (⋃i, A i)) : ∃(t : set ι), mk t = mk θ ∧ is_delta_system (restrict A t) :=
begin
  let nr : ι → ρ → θ := λ i ξ, (h2A i ξ).val,
  let good : ρ → Prop := λ ξ, unbounded θr (range $ λ i, nr i ξ),
  have : ∃ξ : ρ, good ξ,
  { apply unbounded_of_unbounded_Union θr (λ ξ, range $ λ i, nr i ξ),
    { rw [Union_range_eq_Union], exact h3A, intro i, exact (h2A i).to_equiv.bijective.2 },
    { rw [←cof_type, ←θtype_eq, hθ.2], refine lt_trans hρ hκθ }},
  let ξ₀ : ρ := ρwo.wf.min good (ne_empty_iff_exists_mem.mpr this),
  let α₀ : ordinal := sup.{u u} (λ o : {x // ρr x ξ₀}, sup.{u u} $ λ x : ι,
    ordinal.succ $ typein θr $ nr x o.1),
  have hα₀ : α₀ < type θr,
  { rw [←θtype_eq], apply sup_lt_ord_of_is_regular _ hθ,
    { refine lt_of_le_of_lt _ (lt_trans hρ hκθ), rw [card_typein, ←card_type ρr],
    apply card_le_card, apply le_of_lt, apply typein_lt_type },
    rintro ⟨ξ, hξ⟩, refine lt_of_le_of_lt (sup_succ _) _,
    apply (ord_is_limit hθ.1).2, apply lt_of_not_ge, intro h,
    apply ρwo.wf.not_lt_min _ _ _ hξ, apply unbounded_range_of_sup_ge,
    dsimp, rw [←θtype_eq], exact h },
  let pick' : ∀(μ : θ), ∀(pick : ∀y, θr y μ → ι), ordinal :=
  λ μ pick, max α₀ $ sup.{u u} (λ x : ρ × {x // θr x μ}, typein θr $ nr (pick x.2.val x.2.2) x.1),
  have pick'_lt : ∀(μ : θ) (pick : ∀y, θr y μ → ι), pick' μ pick < type θr,
  { intros μ pick,
    apply max_lt hα₀,
    rw [←θtype_eq],
    apply sup_lt_ord_of_is_regular _ hθ,
    { apply @mul_lt_of_lt (mk ρ) (mk {x // θr x μ}) _ hθ.1 (lt_trans hρ hκθ),
      rw [←ord_lt_ord, θtype_eq], apply lt_of_le_of_lt (ord_le_type (subrel θr {x | θr x μ})),
      apply typein_lt_type },
    rintro ⟨x, y, hy⟩, rw [θtype_eq], apply typein_lt_type },
  have : ∀(x : θ), ∃i : ι, θr x (nr i ξ₀),
  { intro x, have : good ξ₀ := ρwo.wf.min_mem good _,
    have θr_unbounded : ∀(x : θ), ∃y, θr x y,
    { intro y, apply has_succ_of_is_limit, rw [←θtype_eq], exact ord_is_limit hθ.1 },
    cases θr_unbounded x with y hy,
    rcases this y with ⟨z, ⟨i, rfl⟩, hz⟩,
    use i, rcases trichotomous_of θr (nr i ξ₀) y with hw | rfl | hw,
    exfalso, exact hz hw, exact hy, exact trans hy hw },
  let pick : θ → ι := θwo.wf.fix
    (λ μ pick, classical.some $ this $ enum θr (pick' μ pick) (pick'_lt μ pick)),
  have lt_pick : ∀(μ : θ),
    θr (enum θr (pick' μ (λ y _, pick y)) (pick'_lt μ (λ y _, pick y))) (nr (pick μ) ξ₀),
  { intro μ, dsimp [pick], rw [θwo.wf.fix_eq _ μ], apply classical.some_spec (this _) },
  have pick_lt_pick : ∀{μ ν : θ} (h : θr ν μ) (η : ρ),
    θr (nr (pick ν) η) (nr (pick μ) ξ₀),
  { intros, apply trans_trichotomous_left _ (lt_pick μ), rw [←typein_le_typein, typein_enum],
    refine le_trans _ (le_max_right _ _), refine le_trans _ (le_sup _ ⟨η, ν, h⟩), refl },
  let sub_α₀ : set θ := typein θr ⁻¹' {c | c < α₀},
  have h1sub_α₀ : mk ↥sub_α₀ = α₀.card,
  { rw [←cardinal.lift_inj.{_ u+1}, mk_preimage_of_injective_of_subset_range_lift],
    rw [mk_initial_seg, cardinal.lift_lift],
    exact injective_typein θr,
    intros o ho,
    rcases typein_surj θr (lt_trans ho hα₀) with ⟨_, rfl⟩,
    apply mem_range_self },
  have h2A2' : ∀{x y : θ}, θr x y → A (pick x) ∩ A (pick y) ⊆ sub_α₀,
  { rintros x y hxy z ⟨hzx, hzy⟩,
    let η := typein (subrel θr $ A $ pick y) ⟨z, hzy⟩,
    have η_def : z = (enum (subrel θr $ A $ pick y) η (typein_lt_type _ _)).val, {rw [enum_typein]},
    cases lt_or_ge η (typein ρr ξ₀) with h h,
    { rw [mem_preimage, mem_set_of_eq],
      refine lt_of_lt_of_le _ (ordinal.le_sup _ _),
      { refine ⟨enum ρr η (lt_trans h (typein_lt_type _ _)), _⟩,
        rw [←typein_lt_typein ρr, typein_enum], exact h },
      refine lt_of_lt_of_le _ (ordinal.le_sup _ (pick y)),
      convert lt_succ_self (typein θr z), rw [η_def],
      dsimp [nr], congr' 1, apply order_iso_enum' (h2A _) },
    exfalso,
    have η_lt : η < type ρr,
    { convert typein_lt_type (subrel θr $ A $ pick y) ⟨z, hzy⟩ using 1, apply quotient.sound,
      exact ⟨h2A (pick y)⟩ },
    have : ¬ρr (enum ρr η η_lt) ξ₀, { rw [←typein_le_typein, typein_enum], exact h },
    apply this,
    rw [(h2A (pick y)).ord], dsimp only [subrel, order.preimage],
    convert pick_lt_pick hxy ((h2A (pick x)).symm ⟨z, hzx⟩) using 1,
    transitivity z, { rw [η_def], congr' 1, apply order_iso_enum (h2A _) },
    transitivity subtype.val ⟨z, hzx⟩, refl,
    congr' 1, symmetry, apply equiv.right_inv },
  have h1A2 : mk (range pick) = mk θ,
  { have increasing_pick : ∀{{x y : θ}}, θr x y → θr (nr (pick x) ξ₀) (nr (pick y) ξ₀),
    { intros x y hxy, apply pick_lt_pick hxy ξ₀ },
    have injective_pick : injective pick,
    { intros x y hx, apply injective_of_increasing _ _ _ increasing_pick, dsimp only,
      congr' 1, exact hx },
    rw [mk_range_eq], apply injective_pick },
  have h2A2 : ∀(x y : range pick), x ≠ y → A x ∩ A y ⊆ sub_α₀,
  { rintro ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨y, rfl⟩⟩ hxy,
    rcases trichotomous_of θr x y with h | h | h,
    apply h2A2' h,
    exfalso, apply hxy, rw h,
    rw [inter_comm], apply h2A2' h },
  have hsub_α₀ : mk ↥sub_α₀ < mk θ,
  { rw [h1sub_α₀, ←ord_lt_ord, θtype_eq], refine lt_of_le_of_lt (ord_card_le _) hα₀ },
  let codomain := {s : set θ // s ⊆ sub_α₀ ∧ mk s ≤ mk ρ},
  have hcodomain : ∀(x : range pick), A x ∩ sub_α₀ ⊆ sub_α₀ ∧ mk (↥(A x ∩ sub_α₀)) ≤ mk ρ,
  { have α₀_lt_pick : ∀(μ : θ), θr (enum θr α₀ hα₀) (nr (pick μ) ξ₀),
    { intro μ, apply trans_trichotomous_left _ (lt_pick μ), rw enum_le_enum, apply le_max_left },
    rintro ⟨s, hs⟩, refine ⟨inter_subset_right _ _, _⟩,
    rcases hs with ⟨μ, rfl⟩, dsimp,
    transitivity mk {x : A (pick μ) // typein θr x.1 < α₀},
    { apply le_of_eq, apply mk_sep },
    let f := (h2A (pick μ)).to_equiv,
    rw [mk_subtype_of_equiv _ f.symm],
    transitivity mk { x : ρ // ρr x ξ₀},
    { apply mk_subtype_mono, intros x hx,
      rw [(h2A (pick μ)).ord], dsimp only [subrel, order.preimage],
      refine trans _ (α₀_lt_pick μ),
      rw [←enum_typein' θr (f x).val, @enum_lt _ θr], exact hx },
    transitivity (typein ρr ξ₀).card, { rw [typein, card_type], refl },
    rw [←card_type ρr], apply card_le_card, apply le_of_lt, apply typein_lt_type },
  let f : range pick → codomain := λx, ⟨A x.1 ∩ sub_α₀, hcodomain x⟩,
  have : ∃r (t : set ι), r ⊆ sub_α₀ ∧ t ⊆ range pick ∧ mk t = mk θ ∧ ∀{{x}}, x ∈ t → A x ∩ sub_α₀ = r,
  { have h1 : cardinal.omega ≤ mk (range pick), { rw [h1A2], exact hθ.1 },
    have h2 : mk codomain < cof (ord $ mk $ range pick),
    { rw [h1A2, hθ.2],
      apply lt_of_le_of_lt (mk_bounded_subset_le _ _),
      refine lt_of_le_of_lt (le_powerlt hρ) (hθ_le _ _),
      apply max_lt hsub_α₀ (lt_of_le_of_lt hκ hκθ) },
    cases infinite_pigeonhole f h1 h2 with r' hr',
    refine ⟨r'.val, subtype.val '' (f ⁻¹' {r'}), _, _, _, _⟩,
    { rintro x hx, exact r'.2.1 hx },
    { rintro _ ⟨⟨x, hx⟩, _, rfl⟩, exact hx },
    { rw [mk_image_eq subtype.val_injective, ←h1A2, ←hr'] },
    { rintro _ ⟨⟨x, hx⟩, hx', rfl⟩,
      simpa only [set.mem_singleton_iff, set.mem_preimage, f, subtype.ext] using hx' }},
  rcases this with ⟨r, t, hr, h1t, h2t, h3t⟩,
  refine ⟨t, h2t, r, _⟩,
  intros x y hxy, rw [←h3t x.2], apply set.ext, intro z, split,
  { intro hz, refine ⟨hz.1, h2A2 ⟨x, h1t x.2⟩ ⟨y, h1t y.2⟩ _ hz⟩,
    intro h, apply hxy, apply subtype.eq, apply congr_arg subtype.val h },
  intro hz, refine ⟨hz.1, _⟩, rw [h3t x.2, ←h3t y.2] at hz, exact hz.1
end

open_locale classical
lemma delta_system_lemma_1 {κ : cardinal} (hκ : cardinal.omega ≤ κ)
  {θ : Type u} (θr : θ → θ → Prop) [θwo : is_well_order θ θr] (hκθ : κ < mk θ)
  (hθ : is_regular $ mk θ) (θtype_eq : ord (mk θ) = type θr) (hθ_le : ∀(β < mk θ), β ^< κ < mk θ)
  {ρ : Type u} (ρr : ρ → ρ → Prop) [ρwo : is_well_order ρ ρr] (hρ : mk ρ < κ)
  {ι : Type u} {A : ι → set θ} (h2A : ∀i, ρr ≃o subrel θr (A i)) (hι : mk θ = mk ι) :
    ∃(t : set ι), mk t = mk θ ∧ is_delta_system (restrict A t) :=
begin
  by_cases h3A : unbounded θr (⋃i, A i),
  { exact delta_system_lemma_2 hκ θr hκθ hθ θtype_eq hθ_le ρr hρ h2A h3A },
  rw [not_unbounded_iff] at h3A, cases h3A with μ hμ,
  let γ := ⋃i, A i,
  let A' : @set.univ ι → {s : set θ // s ⊆ γ ∧ mk s ≤ mk ρ} :=
  λx, ⟨restrict A set.univ x, subset_Union A x.1, _⟩,
  swap, { apply le_of_eq, apply quotient.sound, exact ⟨(h2A x.1).to_equiv.symm⟩ },
  rcases infinite_pigeonhole_set A' (mk θ) _ hθ.1 _ with ⟨R, t, h₁t, h₂t, h₃t⟩,
  have : ∀(x : t), restrict A t x = R.1 := λ x, congr_arg subtype.val (h₃t x.2),
  refine ⟨t, _, R.1, _⟩,
  { apply le_antisymm _ h₂t, rw [hι], apply mk_set_le },
  { intros i j hij, rw [this i, this j, inter_self] },
  { rw [mk_univ, hι] },
  refine lt_of_le_of_lt (mk_bounded_subset_le _ _) _, refine lt_of_le_of_lt (le_powerlt hρ) _,
  rw [hθ.2], apply hθ_le, apply max_lt _ (lt_of_le_of_lt hκ hκθ),
  rw [←ord_lt_ord, θtype_eq],
  apply lt_of_le_of_lt _ (typein_lt_type θr μ),
  rw [ord_le, typein, card_type], apply mk_le_mk_of_subset hμ
end

/-- The delta-system lemma. [Kunen 1980, Theorem 1.6, p49] -/
theorem delta_system_lemma {α ι : Type u} {κ θ : cardinal} (hκ : cardinal.omega ≤ κ) (hκθ : κ < θ)
  (hθ : is_regular θ) (hθ_le : ∀(c < θ), c ^< κ < θ) (A : ι → set α)
  (hA : θ ≤ mk ι) (h2A : ∀i, mk (A i) < κ) :
  ∃(t : set ι), mk t = θ ∧ is_delta_system (restrict A t) :=
begin
  revert hθ hθ_le hκ hκθ hA h2A, refine quotient.induction_on θ _, clear θ, intro θ, intros,
  rcases ord_eq θ with ⟨θr, θwo, θtype_eq⟩,
  rcases le_mk_iff_exists_set.mp hA with ⟨t₁, ht₁⟩,
  resetI,
  let β := ⋃(i ∈ t₁), A i,
  have hβ : mk β ≤ mk θ,
  { refine le_trans (mk_bUnion_le _ _) _, rw [ht₁],
    refine le_trans (mul_le_max_of_omega_le_left _) _, exact hθ.1,
    apply max_le, refl, rw [cardinal.sup_le],
    intro i, apply le_of_lt, apply lt_trans (h2A i.1) hκθ },
  have h2β : A '' t₁ ⊆ powerset (range (subtype.val : β → α)),
  { rintro _ ⟨i, hi, rfl⟩ x hx, refine ⟨⟨x, mem_bUnion hi hx⟩, rfl⟩ },
  have f : β ↪ θ, { exact (classical.choice hβ) },
  let A₀ : ι → set θ := image f ∘ preimage subtype.val ∘ A,
  let κα := κ.ord.out.α,
  let κr := κ.ord.out.r,
  have h3A₀ : ∀(i : t₁), type (subrel θr (A₀ i)) < type κr,
  { rintro ⟨i, hi⟩, rw [type_out, lt_ord, card_type],
    rw [mk_image_eq], rw [mk_preimage_of_injective_of_subset_range], apply h2A i,
    apply subtype.val_injective, apply h2β (mem_image_of_mem _ hi), exact f.2 },
  have hκθ' : mk κα < cof (ord (mk θ)),
  { rw [←card_type κr, type_out, card_ord], convert hκθ, exact hθ.2 },
  let g : t₁ → κα := λ i : t₁, enum κr (type (subrel θr (A₀ i))) (h3A₀ i),
  rcases infinite_pigeonhole_set g (mk θ) (ge_of_eq ht₁) hθ.1 hκθ' with ⟨ρ', t₂, ht₂, h2t₂, h3t₂⟩,
  let ρ := { x : κα | κr x ρ' },
  let ρr := subrel κr ρ,
  have hρ : mk ρ < κ, { exact card_typein_out_lt κ ρ', },
  have h4A₁ : Π(i : t₂), ρr ≃o subrel θr (A₀ i),
  { rintro ⟨i, hi⟩, symmetry,
    have : type (subrel θr (A₀ i)) = typein κr ρ', { rw [← h3t₂ hi, typein_enum], refl },
    exact classical.choice (quotient.exact this) },
  have h4t₂ : mk θ = mk ↥t₂,
  { apply le_antisymm h2t₂, convert mk_le_mk_of_subset ht₂ using 1, rw ht₁, refl },
  rcases delta_system_lemma_1 hκ θr hκθ hθ θtype_eq hθ_le ρr hρ h4A₁ h4t₂ with ⟨t, h1t, h2t⟩,
  refine ⟨subtype.val '' t, _, _⟩,
  { rw [mk_image_eq], exact h1t, exact subtype.val_injective },
  have : is_delta_system (λ(i : t), A₀ i.1) := h2t,
  rw [is_delta_system_image, is_delta_system_preimage_iff] at this,
  rw [is_delta_system_precompose_iff (equiv.set.image subtype.val t subtype.val_injective)],
  convert this using 1, apply funext, rintro ⟨⟨i, hi⟩, h2i⟩,
  simp only [function.comp_app, subtype.coe_mk, equiv.set.image_apply, restrict],
  apply subtype.val_injective, intro i, refine h2β (mem_image_of_mem _ $ ht₂ i.1.2), exact f.2
end

theorem delta_system_lemma_uncountable {α : Type u} {ι : Type v}
  (A : ι → set α) (h : cardinal.omega < mk ι) (h2A : ∀i, finite (A i)) :
  ∃(t : set ι), cardinal.omega < mk t ∧ is_delta_system (restrict A t) :=
begin
  have :  ∀ (c : cardinal), c < succ omega → c ^< omega < succ omega,
  { intros c hc, refine lt_of_le_of_lt (powerlt_omega_le _) _,
    apply max_lt hc (lt_succ_self _) },
  rcases delta_system_lemma (le_refl _) (lt_succ_self _) (succ_is_regular (le_refl _)) this
    (image ulift.up.{v u} ∘ A ∘ ulift.down.{u v}) _ _ with ⟨t, h1t, h2t⟩,
  refine ⟨ulift.down '' t, _, _⟩,
  { rw [←cardinal.lift_lt.{_ max u v}, mk_image_eq_lift, h1t, cardinal.lift_succ,
      cardinal.lift_omega, cardinal.lift_omega], apply cardinal.lt_succ_self,
      apply equiv.ulift.bijective.1 },
  { rw [restrict, is_delta_system_image] at h2t, swap, exact equiv.ulift.symm.bijective.1,
    rw [is_delta_system_precompose_iff (equiv.set.image _ _ _)],
    swap, exact equiv.ulift.bijective.1,
    convert h2t, apply funext, rintro ⟨x, hx⟩, refl },
  { rw [←cardinal.lift_lt, cardinal.lift_omega, ←cardinal.succ_le] at h, exact h },
  rintro ⟨i⟩, rw [lt_omega_iff_finite], apply finite_image, exact h2A i
end

end delta_system

namespace set

variables {α β : Type u}
open cardinal subtype

/- currently the proof depends on cardinal numbers -/
lemma finite_of_finite_image_of_inj_on (f : α → β) (s : set α) (hf : inj_on f s)
  (h : finite (f '' s)) : finite s :=
by { rw [←lt_omega_iff_finite] at h ⊢, rwa [mk_image_eq_of_inj_on f s hf] at h }

/- currently the proof depends on cardinal numbers -/
lemma countable_of_embedding {s : set α} {t : set β} (f : s ↪ t) (h : countable t) : countable s :=
begin
  rw [countable_iff], rw [countable_iff] at h,
  refine le_trans _ h, refine ⟨f⟩
end

/- maybe generalize eq_on -/
def eq_on' {α} {β : α → Type*} (f g : ∀x, β x) (s : set α) : Prop :=
∀{{x}}, x ∈ s → f x = g x

lemma eq_on'_iff {α} {β : α → Type*} (f g : ∀x, β x) (s : set α) :
  eq_on' f g s ↔ restrict f s = restrict g s :=
begin
  split, intros h, apply funext, rintro ⟨x, hx⟩, exact h hx,
  intros h x hx, apply congr_fun h ⟨x, hx⟩
end

end set

-- namespace topological_space

open set topological_space cardinal subtype (restrict)

section CCC
variables (α : Type u) [topological_space α]

def countable_chain_condition : Prop :=
∀(s : set (set α)), (∀{{o}}, o ∈ s → is_open o) → pairwise_disjoint s → s.countable

variable {α}
lemma countable_chain_condition_of_nonempty
  (h : ∀(s : set (set α)), (∀{{o}}, o ∈ s → o ≠ ∅) → (∀{{o}}, o ∈ s → is_open o) →
  pairwise_disjoint s → s.countable) : countable_chain_condition α :=
begin
  intros s open_s hs,
  let s' : set (set α) := s \ {∅},
  have hs' : ∀{{o : set α}}, o ∈ s' → o ≠ ∅,
  { intros o ho h2o, apply ho.2, rw [mem_singleton_iff, h2o] },
  have open_s' : ∀{{o : set α}}, o ∈ s' → is_open o,
  { intros o ho, exact open_s (diff_subset _ _ ho), },
  have h2s' : pairwise_disjoint s',
  { refine pairwise_disjoint_subset _ hs, apply diff_subset },
  have : countable (insert ∅ s'), { apply countable_insert (h s' hs' open_s' h2s') },
  apply countable_subset _ this,
  rw [insert_diff_singleton], apply subset_insert
end

lemma countable_chain_condition_of_topological_basis (B : set (set α))
  (hB : is_topological_basis B)
  (h : ∀(s : set (set α)), s ⊆ B →
  pairwise_disjoint s → s.countable) : countable_chain_condition α :=
begin
  apply countable_chain_condition_of_nonempty,
  intros s s_nonempty s_open hs,
  have f : ∀(x : s), { y : set α // y ∈ B ∧ y ≠ ∅ ∧ y ⊆ x.1 },
  { rintro ⟨x, hx⟩, apply classical.subtype_of_exists,
    have : ∃y, y ∈ x, { exact ne_empty_iff_exists_mem.mp (s_nonempty hx) },
    cases this with y hy,
    rcases mem_basis_subset_of_mem_open hB hy (s_open hx) with ⟨h₁, h₂, h₃, h₄⟩,
    refine ⟨h₁, h₂, _, h₄⟩, rw [ne_empty_iff_exists_mem], exact ⟨_, h₃⟩ },
  let s' : set (set α) := range (λ(x : s), (f x).1),
  have hs' : ∀{{o : set α}}, o ∈ s' → o ∈ B,
  { rintro _ ⟨o, rfl⟩, exact (f o).2.1 },
  have h2s' : pairwise_disjoint s',
  { apply pairwise_disjoint_range _ _ hs, intro x, exact (f x).2.2.2 },
  have := h s' hs' h2s',
  rw [cardinal.countable_iff] at this ⊢, convert this using 1, rw [mk_range_eq],
  rintro x x' hxx',
  have : ∃y, y ∈ (f x).1, { exact ne_empty_iff_exists_mem.mp (f x).2.2.1 },
  cases this with y hy,
  apply subtype.eq, apply pairwise_disjoint_elim hs x.2 x'.2 y ((f x).2.2.2 hy),
  dsimp only at hxx', rw hxx' at hy, exact (f x').2.2.2 hy
end

lemma countable_chain_condition_of_separable_space [h : separable_space α] :
  countable_chain_condition α :=
begin
  have := h, rcases this with ⟨⟨D, h1D, h2D⟩⟩, rw [dense_iff_inter_open] at h2D,
  apply countable_chain_condition_of_nonempty, intros C h1C h2C h3C,
  refine countable_of_embedding _ h1D,
  have f : ∀(c : C), Σ'(d : D), d.1 ∈ c.1,
  { rintro ⟨s, hs⟩, have := h2D s (h2C hs) (h1C hs),
    rw [ne_empty_iff_exists_mem] at this,
    rcases classical.subtype_of_exists this with ⟨x, ⟨hx, h2x⟩⟩,
    exact ⟨⟨x, h2x⟩, hx⟩ },
  refine ⟨λ c, (f c).1, _⟩,
  rintros ⟨s, hs⟩ ⟨s', hs'⟩ hss',
  rw [subtype.ext], dsimp,
  apply pairwise_disjoint_elim h3C hs hs' (f ⟨s, hs⟩).1 (f ⟨s, hs⟩).2,
  dsimp only at hss', rw [hss'], exact (f ⟨s', hs'⟩).2
end

lemma countable_chain_condition_of_countable (h : mk α ≤ omega) : countable_chain_condition α :=
begin
  haveI : separable_space α := ⟨⟨set.univ, by rwa [countable_iff, mk_univ], closure_univ⟩⟩,
  apply countable_chain_condition_of_separable_space,
end

end CCC

section pi

variables {α : Type u} {β : α → Type v} [∀x, topological_space (β x)]
          {γ : Type w} [topological_space γ]

def standard_open {i : α} (o : opens (β i)) : set (Πx, β x) :=
{f : Πx, β x | f i ∈ o }

variable (β)
def pi_subbasis : set (set (Πx, β x)) :=
range (λ(x : Σ(i : α), opens (β i)), standard_open x.2)

variable {β}

variable (β)
lemma is_subbasis_pi : Pi.topological_space = generate_from (pi_subbasis β) :=
begin
  symmetry, apply le_antisymm,
  { refine lattice.le_infi _, intro i,
    rintro _ ⟨s, hs, rfl⟩, apply generate_open.basic, exact ⟨⟨i, s, hs⟩, rfl⟩ },
  { rw [le_generate_from_iff_subset_is_open], rintro _ ⟨⟨i, o, ho⟩, rfl⟩,
    apply generate_open.basic, apply mem_bUnion (mem_range_self i), exact ⟨o, ho, rfl⟩ }
end

def pi_basis : set (set (Πx, β x)) :=
(λf, ⋂₀ f) '' {f : set (set (Πx, β x)) | finite f ∧ f ⊆ pi_subbasis β ∧ ⋂₀ f ≠ ∅ }

lemma pi_basis_eq : pi_basis β =
  {g | ∃(s:Πx, set (β x)) (i : finset α), (∀x∈i, is_open (s x)) ∧ g = pi ↑i s} \ {∅} :=
begin
  apply subset.antisymm, swap,
  { rintro _ ⟨⟨s, i, hs, rfl⟩, hs'⟩,
    let O : (↑i : set α) → set (Πx, β x) := (λ x, standard_open ⟨s x.1, hs x.1 x.2⟩),
    have : ⋂₀ range O = pi ↑i s,
    { apply subset.antisymm,
      { rintro f hf x hx, exact hf (O ⟨x, hx⟩) (mem_range_self _) },
      { rintro f hf _ ⟨x, rfl⟩, exact hf x.1 x.2 } },
    refine ⟨range O, ⟨finite_range _, _, _⟩, this⟩,
    { rintro _ ⟨x, rfl⟩, dsimp only, refine ⟨⟨x.1, ⟨s x.1, hs x.1 x.2⟩⟩, rfl⟩ },
    { rw [this], exact mt mem_singleton_iff.mpr hs' } },
  rintro _ ⟨o, ⟨h1o, h2o, h3o⟩, rfl⟩, dsimp only, refine ⟨_, mt mem_singleton_iff.mp h3o⟩,
  rw [pi_subbasis, subset_range_iff] at h2o, rcases h2o with ⟨o', rfl, _⟩,
  let γ := Σi, opens (β i),
  let O := (λ (x : γ), standard_open (x.snd)),
  have hβ : nonempty (Πx, β x),
  { rw [←coe_nonempty_iff_ne_empty] at h3o, rcases h3o with ⟨f, hf⟩, exact ⟨f⟩ },
  have ho' : ∀(x ∈ o'), (x : γ).2.1 ≠ ∅,
  { rintros ⟨x, o⟩ ho, refine mt _ h3o, intro h,
    rw [eq_empty_iff_forall_not_mem], intros f hf, rw [eq_empty_iff_forall_not_mem] at h,
    apply h (f _), exact hf _ (mem_image_of_mem _ ho) },
  let o'' := {x ∈ o' | (x : γ).2.1 ≠ univ },
  let i := sigma.fst '' o'',
  have h2o' : finite o'',
  { refine finite_of_finite_image_of_inj_on O _ _ _,
    { haveI : decidable_eq α := λ _ _, classical.prop_decidable _,
      rintro ⟨x, o⟩ ⟨x', o'⟩ hx hx' hoo', cases hβ with f,
      have h₁ : nonempty o.1, { rw [coe_nonempty_iff_ne_empty], exact ho' _ hx.1 },
      have h₂ : nonempty (-o.1 : set (β x)), { rw [nonempty_compl], exact hx.2 },
      rcases h₁ with ⟨z₁, hz₁⟩, rcases h₂ with ⟨z₂, hz₂⟩,
      let f₁ : Πx', β x' := change f z₁,
      let f₂ : Πx', β x' := change f z₂,
      have hf₁ : f₁ ∈ O ⟨x, o⟩, { simp [O, standard_open, f₁, change], exact hz₁ },
      have hf₂ : f₂ ∉ O ⟨x, o⟩, { simp [O, standard_open, f₂, change], exact hz₂ },
      rw [hoo'] at hf₁ hf₂,
      have : x = x',
      { by_contradiction h',
        have : f₁ x' ≠ f₂ x', { refine mt _ hf₂,
        dsimp only [O, standard_open, mem_sep, mem_set_of_eq], intro h, rw ←h, exact hf₁ },
        apply this, simp [f₁, f₂, change, h'] },
      subst this, apply congr_arg (sigma.mk x), apply subtype.eq, apply set.ext, intro z,
      rw [set.ext_iff] at hoo',
      simpa [O, standard_open, change] using hoo' (change f z) },
    apply finite_subset h1o, apply image_subset, apply sep_subset } ,
  have hi : finite i,
  { refine finite_image _  h2o' },
  haveI : ∀x, decidable (x ∈ i) := λ x, classical.prop_decidable _,
  let C : Πx, set (β x) :=
  λ x, if h : x ∈ i then ⋂₀ { O | ∃h : _root_.is_open O, (⟨x, ⟨O, h⟩⟩ : γ) ∈ o'' } else univ,
  refine ⟨C, finite.to_finset hi, _, _⟩,
  { intros x hx, rw [finite.mem_to_finset] at hx, have := hx,
    rcases this with ⟨⟨x, u⟩, ⟨hu, hu'⟩, rfl⟩,
    simp only [C, dif_pos hx],
    apply is_open_sInter,
    { have : finite (subtype.val '' ((λ s : opens (β x), sigma.mk x s) ⁻¹' o'')),
      { apply finite_image, apply finite_preimage _ h2o', finish },
      convert this,
      apply subset.antisymm,
      { rintro o ⟨h1o, h2o⟩, exact ⟨⟨o, h1o⟩, h2o, rfl⟩ },
      rintro _ ⟨⟨o, ho⟩, h2o, rfl⟩, refine ⟨ho, h2o⟩ },
    rintro s ⟨hs, hs'⟩, exact hs },
  apply subset.antisymm,
  { rintro f hf x hx, rw [finite.coe_to_finset] at hx, have := hx,
    rcases this with ⟨⟨x, o⟩, ⟨ho, h2o⟩, rfl⟩,
    simp only [C, dif_pos hx], rintro s ⟨hs, h2s⟩,
    exact hf _ (mem_image_of_mem _ h2s.1) },
  rintro f hf _ ⟨⟨x, o⟩, ho, rfl⟩, dsimp [standard_open], rw [finite.coe_to_finset] at hf,
  haveI : decidable (o.1 = univ) := classical.prop_decidable _,
  by_cases ho' : o.1 = univ, { rw [mem_opens, ho'], apply mem_univ },
  have hx : x ∈ i, { refine ⟨⟨x, o⟩, ⟨ho, ho'⟩, rfl⟩ },
  have : C x ⊆ o.1,
  { cases o with o h2o, simp only [C, dif_pos hx], rintro z hz, exact hz o ⟨h2o, ⟨ho, ho'⟩⟩ },
  exact this (hf x hx),
end

variable {β}

lemma nonempty_of_mem_pi_basis {o : set (Πx, β x)} (h : o ∈ pi_basis β) : nonempty o :=
by { rcases h with ⟨o, ho, rfl⟩, rw [coe_nonempty_iff_ne_empty], exact ho.2.2 }

variable (β)
lemma is_topological_basis_pi : is_topological_basis (pi_basis β) :=
is_topological_basis_of_subbasis (is_subbasis_pi β)

variable {β}

open_locale classical
lemma is_open_map_apply (i : α) : is_open_map (λf : Πi, β i, f i) :=
begin
  apply is_open_map_of_is_topological_basis (is_topological_basis_pi β),
  intros o ho,
  rw [pi_basis_eq] at ho, rcases ho with ⟨⟨s, t, hs, rfl⟩, hs'⟩,
  have : nonempty (pi ↑t s), { rw [←nmem_singleton_empty], exact hs' },
  by_cases i ∈ t, { rw [image_pi_pos ↑t s this i h], exact hs i h },
  rw [image_pi_neg ↑t s this i h], exact is_open_univ
end

lemma restrict_image_pi (t : set α) (s : set α) (s' : Πi, set (β i))
  (h : nonempty (pi t s')) :
  (λ(f : Πi, β i), restrict f s) '' pi t s' = pi (subtype.val ⁻¹' t) (λi, s' i.1) :=
begin
  apply subset.antisymm,
  { rintro _ ⟨f, hf, rfl⟩ i hi, exact hf _ hi },
  rintro f hf, have := h, rcases this with ⟨f', hf'⟩,
  refine ⟨λ i, if h : i ∈ s then f ⟨i, h⟩ else f' i, _, _⟩,
  { intros i hi, dsimp only,
    by_cases h2i : i ∈ s,
    { rw [dif_pos h2i], exact hf ⟨i, h2i⟩ hi, },
    { rw [dif_neg h2i], exact hf' i hi } },
  apply funext, rintro ⟨i, hi⟩, dsimp only, rw [restrict], apply dif_pos hi
end

lemma is_open_map_restrict (s : set α) : is_open_map (λ(f : Πi, β i), restrict f s) :=
begin
  apply is_open_map_of_is_topological_basis (is_topological_basis_pi β),
  intros o ho,
  rw [pi_basis_eq] at ho, rcases ho with ⟨⟨s', t, hs, rfl⟩, hs'⟩,
  have : nonempty (pi ↑t s'), { rw [←nmem_singleton_empty], exact hs' },
  rw [restrict_image_pi _ _ _ this],
  apply is_open_of_is_topological_basis (is_topological_basis_pi _),
  rw [pi_basis_eq], refine ⟨⟨λ x, s' x.1, _, _, _⟩, _⟩,
  { apply finite.to_finset, apply finite_preimage (inj_on_of_injective _ subtype.val_injective),
    exact t.finite_to_set },
  { intros x hx, rw [finite.mem_to_finset] at hx, exact hs _ hx },
  { congr' 1, ext, rw [finite.coe_to_finset] },
  dsimp only, rw [nmem_singleton_empty],
  rcases this with ⟨f, hf⟩, exact ⟨⟨λ i, f i.1, λ i hi, hf i.1 hi⟩⟩
end

/- The set of indices where a set o is constant, i.e. that coordinate doesn't matter for
  deciding whether a point is in o -/
def support (o : set (Πx, β x)) : set α :=
⋂₀ { s : set α | ∀{{f g : Πi, β i}}, eq_on' f g s → f ∈ o → g ∈ o }

lemma support_pi (i : set α) (s : ∀x, set (β x)) (h : nonempty $ pi i s) :
  support (pi i s) = {x ∈ i | s x ≠ set.univ } :=
begin
  apply subset.antisymm,
  { apply sInter_subset_of_mem, intros f g hfg hf x hx,
    by_cases h : s x = univ, rw [h], trivial,
    rw [←hfg ⟨hx, h⟩], exact hf x hx },
  { apply subset_sInter, rintro j hj x ⟨hx, hs⟩,
    have := h, rcases this with ⟨f, hf⟩,
    have h₂ : nonempty (-(s x) : set _), { rw [nonempty_compl], exact hs },
    rcases h₂ with ⟨z₂, hz₂⟩,
    let f₂ : Πx', β x' := change f z₂,
    have hf₂ : f₂ ∉ pi i s, { refine mt _ hz₂, intro hf₂, convert hf₂ x hx,
    simp only [f₂, change, dif_pos] },
    by_contradiction h2x, apply hf₂, apply hj _ hf,
    intros x' hx',
    have hxx' : x ≠ x', { refine mt _ h2x, intro h, rw h, exact hx' },
    simp only [f₂, change, dif_neg hxx'] }
end

lemma support_elim {o : set (Πx, β x)} {f g : Πx, β x} (ho : o ∈ pi_basis β)
  (h : eq_on' f g (support o)) (hf : f ∈ o) : g ∈ o :=
begin
  rw [pi_basis_eq] at ho, rcases ho with ⟨⟨s, i, hs, rfl⟩, hs'⟩,
  have : nonempty (pi ↑i s), { rw [←nmem_singleton_empty], exact hs' },
  intros x hx, rw [support_pi _ _ this] at h,
  by_cases h' : s x = univ, rw [h'], trivial,
  rw [← h ⟨hx, h'⟩], exact hf x hx
end

lemma finite_support_of_pi_subbasis {o : set (Πx, β x)} (h : o ∈ pi_subbasis β) :
  finite (support o) :=
begin
  rcases h with ⟨⟨i, o⟩, rfl⟩,
  apply finite_subset (finite_singleton i),
  apply sInter_subset_of_mem, dsimp [standard_open],
  intros f g hfg hf, rwa [hfg (mem_singleton i)] at hf
end

lemma finite_support_of_pi_basis {o : set (Πx, β x)} (h : o ∈ pi_basis β) :
  finite (support o) :=
begin
  rcases h with ⟨s, ⟨hs, h2s, h3s⟩, rfl⟩,
  apply finite_subset (finite_bUnion' support hs $ λ i hi, finite_support_of_pi_subbasis $ h2s hi),
  apply sInter_subset_of_mem, dsimp only, intros f g hfg hf,
  intros t ht,
  apply support_elim _ _ (hf t ht),
  { apply subbasis_subset_basis, split,
    exact h2s ht, refine mt _ h3s, rw [mem_singleton_iff], rintro rfl,
    refine subset.antisymm _ (empty_subset _), exact sInter_subset_of_mem ht },
  intros x hx, apply hfg, exact mem_bUnion ht hx
end

def extend (g₁ g₂ : Πx, β x) (s : set α) (x : α) : β x :=
if h : x ∈ s then g₁ x else g₂ x

open delta_system
theorem countable_chain_condition_pi
  (h : ∀(s : set α), finite s → countable_chain_condition (Π(x : s), β x)) :
  countable_chain_condition (Πx, β x) :=
begin
  apply countable_chain_condition_of_topological_basis _ (is_topological_basis_pi β),
  intros C hC h2C, rw [countable_iff], apply le_of_not_gt, intro h3C,
  let A : C → set α := λ s, support s.1,
  have h2A : ∀ (s : C), finite (A s),
  { rintro ⟨s, hs⟩, apply finite_support_of_pi_basis, exact hC hs },
  rcases delta_system_lemma_uncountable A h3C h2A with ⟨C', h1C', ⟨R, hR⟩⟩,
  have h3A' : 2 ≤ mk C',
    { apply le_of_lt, refine lt_trans _ h1C', convert cardinal.nat_lt_omega 2,
      rw [nat.cast_bit0, nat.cast_one] },
  have h2R : finite R,
  { apply finite_root h3A' _ hR, intro s, exact h2A s.1 },
  let C'' := subtype.val '' C',
  have hC'' : C'' ⊆ C, { rintro _ ⟨⟨x, hx⟩, h2x, rfl⟩, exact hx },
  let π : (Πx, β x) → Π(x : R), β x := λ f, restrict f R,
  let D : set (set (Π(x : R), β x)) := image π '' C'',
  have hD : ∀ ⦃o : set (Π (x : R), β x)⦄, o ∈ D → is_open o,
  { rintro _ ⟨o, ho, rfl⟩, apply is_open_map_restrict,
    apply is_open_of_is_topological_basis (is_topological_basis_pi β) (hC $ hC'' ho) },
  have h2'D : ∀(s t : set (Πx, β x)), s ∈ C'' → t ∈ C'' → s ≠ t → disjoint (π '' s) (π '' t),
  { rintro s t hs ht hst,
    rw [disjoint_iff_eq_empty, eq_empty_iff_forall_not_mem],
    rintro f ⟨hfs, hft⟩,
    have := h2C _ (hC'' hs) _ (hC'' ht) (λ h, hst $ by rw h),
    rcases hfs with ⟨g₁, hg₁, rfl⟩,
    rcases hft with ⟨g₂, hg₂, hg⟩,
    rw [disjoint_iff_eq_empty, eq_empty_iff_forall_not_mem] at this,
    apply this (extend g₁ g₂ (support s)),
    split, { apply support_elim (hC (hC'' hs)) _ hg₁, intros x hx, rw [extend, dif_pos hx] },
    apply support_elim (hC (hC'' ht)) _ hg₂, intros x hx,
    by_cases x ∈ support s,
    { rw [extend, dif_pos h], rw [←eq_on'_iff] at hg, apply hg,
      rcases hs with ⟨s', hs', rfl⟩, rcases ht with ⟨t', ht', rfl⟩,
      rw [←@hR ⟨s', hs'⟩ ⟨t', ht'⟩], exact ⟨h, hx⟩, intro h, apply hst,
      apply congr_arg subtype.val (congr_arg subtype.val h) },
    rw [extend, dif_neg h] },
  have h2D : pairwise_disjoint D,
  { rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ hst, apply h2'D s t hs ht, intro h, apply hst, rw h },
  have h3D : cardinal.omega < mk D,
  { rw [mk_image_eq_of_inj_on, mk_image_eq], exact h1C',
    apply subtype.val_injective,
    intros s t hs ht hst, by_contradiction hst',
    apply ne_of_disjoint _ (h2'D s t hs ht hst') hst,
    apply coe_nonempty_iff_ne_empty.mp,
    apply nonempty_image, apply nonempty_of_mem_pi_basis (hC $ hC'' hs) },
  apply not_le_of_gt h3D, rw [←countable_iff], exact h R h2R D hD h2D
end

end pi
