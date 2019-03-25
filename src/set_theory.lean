import .to_mathlib

/-
note: in comment above cofinality, change sentence with
+  `∀ a, ∃ b ∈ S, ¬(b > a)`. It is defined for all ordinals, but
-/

universe variables u v w
noncomputable theory

section subtype
open function subtype
def subtype.coind {α β} (f : α → β) {p : β → Prop} (h : ∀a, p (f a)) : α → subtype p :=
λ a, ⟨f a, h a⟩

/- note: almost the same as `cod_restrict` -/
theorem subtype.coind_injective {α β} {f : α → β} {p : β → Prop} (h : ∀a, p (f a))
  (hf : injective f) : injective (subtype.coind f h) :=
λ x y hxy, hf $ by apply congr_arg subtype.val hxy
end subtype

namespace function
open set
variables {α : Type u} {β : Type v}
lemma injective_of_increasing (r : α → α → Prop) (s : β → β → Prop) [is_trichotomous α r]
  [is_irrefl β s] (f : α → β) (hf : ∀{x y}, r x y → s (f x) (f y)) : injective f :=
begin
  intros x y hxy,
  rcases trichotomous_of r x y with h | h | h,
  have := hf h, rw hxy at this, exfalso, exact irrefl_of s (f y) this,
  exact h,
  have := hf h, rw hxy at this, exfalso, exact irrefl_of s (f y) this
end

namespace embedding
protected def subtype_map {p : α → Prop} {q : β → Prop} (f : α ↪ β)
  (h : ∀{{x}}, p x → q (f x)) : {x : α // p x} ↪ {y : β // q y} :=
⟨λ x, ⟨f x.1, h x.2⟩, subtype.coind_injective _ $ injective_comp f.2 subtype.val_injective⟩

protected def image (f : α ↪ β) : set α ↪ set β :=
⟨image f, injective_image f.2⟩

end embedding

end function


namespace equiv

variables {α : Type u} {β : Type v}

def set_congr (e : α ≃ β) : set α ≃ set β :=
⟨λ s, e '' s, λ t, e.symm '' t, symm_image_image e, symm_image_image e.symm⟩

def subtype_congr {p q : α → Prop} (e : ∀x, p x ↔ q x) : subtype p ≃ subtype q :=
⟨λ x, ⟨x.1, (e x.1).1 x.2⟩, λ x, ⟨x.1, (e x.1).2 x.2⟩,
 λ ⟨x, hx⟩, subtype.eq rfl, λ ⟨x, hx⟩, subtype.eq rfl⟩

@[simp] lemma subtype_congr_mk {p q : α → Prop} (e : ∀x, p x ↔ q x)
  {x : α} (h : p x) : subtype_congr e ⟨x, h⟩ = ⟨x, (e x).1 h⟩ := rfl

end equiv

namespace Well_order

attribute [instance] Well_order.wo
instance (W : Well_order) : decidable_linear_order W.α :=
decidable_linear_order_of_is_well_order W.r

end Well_order

namespace set
variables {α : Type u} {β : Type v}
/-- an unbounded or cofinal set -/
def unbounded (r : α → α → Prop) (s : set α) : Prop := ∀ a, ∃ b ∈ s, ¬ r b a
/-- a bounded or final set -/
def bounded (r : α → α → Prop) (s : set α) : Prop := ∃a, ∀ b ∈ s, r b a
end set
open set
namespace well_founded
protected def sup {α} {r : α → α → Prop} (wf : well_founded r) (s : set α) (h : bounded r s) : α :=
wf.min { x | ∀a ∈ s, r a x } (set.ne_empty_of_exists_mem h)

protected def lt_sup {α} {r : α → α → Prop} (wf : well_founded r) {s : set α} (h : bounded r s)
  {x} (hx : x ∈ s) : r x (wf.sup s h) :=
min_mem wf { x | ∀a ∈ s, r a x } (set.ne_empty_of_exists_mem h) x hx

protected def succ {α} {r : α → α → Prop} (wf : well_founded r) (x : α) (h : ∃y, r x y) : α :=
wf.min { y | r x y } (set.ne_empty_of_exists_mem h)

protected lemma lt_succ {α} {r : α → α → Prop} (wf : well_founded r) {x : α} (h : ∃y, r x y) :
  r x (wf.succ x h) :=
min_mem _ _ _

protected lemma lt_succ_iff {α} {r : α → α → Prop} [wo : is_well_order α r] {x : α} (h : ∃y, r x y)
  (y : α) : r y (wo.wf.succ x h) ↔ r y x ∨ y = x :=
begin
  split,
  { intro h, have : ¬r x y, intro hy, exact wo.wf.not_lt_min _ _ hy h,
    rcases trichotomous_of r x y with hy | hy | hy,
    exfalso, exact this hy,
    right, exact hy.symm,
    left, exact hy },
  rintro (hy | rfl), exact trans hy (wo.wf.lt_succ h), exact wo.wf.lt_succ h
end

end well_founded

namespace cardinal
open function equiv

variables {α β : Type u}

lemma zero_power_le (c : cardinal.{u}) : (0 : cardinal.{u}) ^ c ≤ 1 :=
by { by_cases h : c = 0, rw [h, power_zero], rw [zero_power h], exact le_of_lt zero_lt_one }

lemma mul_le_max_of_omega_le_left {a b : cardinal} (h : omega ≤ a) : a * b ≤ max a b :=
begin
  convert mul_le_mul (le_max_left a b) (le_max_right a b), rw [mul_eq_self],
  refine le_trans h (le_max_left a b)
end

lemma mul_eq_max_of_omega_le_left {a b : cardinal} (h : omega ≤ a) (h' : b ≠ 0) : a * b = max a b :=
begin
  apply le_antisymm, apply mul_le_max_of_omega_le_left h,
  cases le_or_gt omega b with hb hb, rw [mul_eq_max h hb],
  have : b ≤ a, exact le_trans (le_of_lt hb) h,
  rw [max_eq_left this], convert mul_le_mul_left _ (one_le_iff_ne_zero.mpr h'), rw [mul_one],
end

lemma add_one_eq {a : cardinal} (ha : omega ≤ a) : a + 1 = a :=
have 1 ≤ a, from le_trans (le_of_lt one_lt_omega) ha,
by simp only [max_eq_left, add_eq_max, ha, this]

lemma succ_ne_zero (c : cardinal) : succ c ≠ 0 :=
by { rw [←pos_iff_ne_zero, lt_succ], apply zero_le }

lemma mk_univ (α : Type u) : mk (@set.univ α) = mk α :=
quotient.sound ⟨equiv.set.univ α⟩

lemma mk_set_le {α : Type u} (s : set α) : mk s ≤ mk α :=
⟨⟨subtype.val, subtype.val_injective⟩⟩

lemma mk_le_of_subset {s t : set α} (h : s ⊆ t) : mk s ≤ mk t :=
⟨embedding_of_subset h⟩

lemma mk_le_of_subproperty {p q : α → Prop} (h : ∀x, p x → q x) : mk {x // p x} ≤ mk {x // q x} :=
⟨embedding_of_subset h⟩

lemma mk_le_of_surjective (f : α → β) (h : surjective f) : mk β ≤ mk α :=
⟨embedding.of_surjective h⟩

lemma mk_image_le (f : α → β) (s : set α) : mk (f '' s) ≤ mk s :=
begin
  fapply mk_le_of_surjective,
  { rintro ⟨x, hx⟩, exact ⟨f x, mem_image_of_mem f hx⟩ },
  { rintro ⟨y, ⟨x, hx, h⟩⟩, exact ⟨⟨x, hx⟩, subtype.eq h⟩ }
end

lemma mk_image_eq (f : α → β) (s : set α) (h : injective f) : mk (f '' s) = mk s :=
quotient.sound ⟨(equiv.set.image f s h).symm⟩

lemma mk_image_eq_of_inj_on (f : α → β) (s : set α) (h : inj_on f s) : mk (f '' s) = mk s :=
le_antisymm (mk_image_le f s) $ ⟨⟨λ⟨x, hx⟩, ⟨f x, mem_image_of_mem f hx⟩,
  λ⟨x, hx⟩ ⟨x', hx'⟩ hxx', subtype.eq $ h hx hx' $ by apply congr_arg subtype.val hxx'⟩⟩

lemma mk_range_le (f : α → β) : mk (range f) ≤ mk α :=
begin
  fapply mk_le_of_surjective,
  { intro x, exact ⟨f x, mem_range_self x⟩ },
  { intro y, rcases y.2 with ⟨x, h⟩, exact ⟨x, subtype.eq h⟩ }
end

lemma mk_range_eq (f : α → β) (h : injective f) : mk (range f) = mk α :=
quotient.sound ⟨(equiv.set.range f h).symm⟩

lemma mk_subtype_of_equiv (p : α → Prop) (e : α ≃ β) :
  mk {a : α // p a} = mk {b : β // p (e.symm b)} :=
quotient.sound ⟨subtype_equiv_of_subtype e⟩

lemma mk_sUnion {α : Type u} (A : set (set α)) :
  mk (⋃₀ A) ≤ mk A * cardinal.sup.{u u} (λ s : A, mk s) :=
by { rw [sUnion_eq_Union], refine le_trans mk_Union_le_sum_mk (sum_le_sup _) }

lemma finset_card_lt_omega (s : finset α) : mk (↑s : set α) < omega :=
by { rw [lt_omega_iff_fintype], exact ⟨finset.subtype.fintype s⟩ }

-- lemma mk_set (α : Type u) : mk (set α) = 2 ^ mk α :=
-- sorry

lemma mk_preimage_of_injective_lift {α : Type u} {β : Type v} (f : α → β) (s : set β)
  (h : injective f) : lift.{u v} (mk (f ⁻¹' s)) ≤ lift.{v u} (mk s) :=
begin
  constructor, apply embedding.congr equiv.ulift.symm equiv.ulift.symm,
  refine ⟨subtype.coind (λ x, f x.1) (λ x, x.2), _⟩,
  apply subtype.coind_injective, exact injective_comp h subtype.val_injective
end

lemma mk_preimage_of_injective_of_onto_lift {α : Type u} {β : Type v} (f : α → β) (s : set β)
  (h : injective f) (h2 : s ⊆ range f) : lift.{u v} (mk (f ⁻¹' s)) = lift.{v u} (mk s) :=
begin
  apply le_antisymm (mk_preimage_of_injective_lift f s h),
  constructor, apply embedding.congr equiv.ulift.symm equiv.ulift.symm,
  fsplit,
  { rintro ⟨y, hy⟩, rcases classical.psigma_of_exists (h2 hy) with ⟨x, rfl⟩, exact ⟨x, hy⟩ },
  rintro ⟨y, hy⟩ ⟨y', hy'⟩, dsimp,
  rcases classical.psigma_of_exists (h2 hy) with ⟨x, rfl⟩,
  rcases classical.psigma_of_exists (h2 hy') with ⟨x', rfl⟩,
  simp [h]
end

lemma mk_preimage_of_injective (f : α → β) (s : set β) (h : injective f) :
  mk (f ⁻¹' s) ≤ mk s :=
by { convert mk_preimage_of_injective_lift.{u u} f s h using 1; rw [lift_id] }

lemma mk_preimage_of_injective_of_onto (f : α → β) (s : set β)
  (h : injective f) (h2 : s ⊆ range f) : mk (f ⁻¹' s) = mk s :=
by { convert mk_preimage_of_injective_of_onto_lift.{u u} f s h h2 using 1; rw [lift_id] }

-- lemma mk_preimage_of_bijective (f : α → β) (s : set β) (h : bijective f) :
--   mk (f ⁻¹' s) = mk s :=
-- sorry

-- lemma mk_preimage_of_equiv (f : α ≃ β) (s : set β) : mk (f ⁻¹' s) = mk s :=
-- mk_preimage_of_bijective _ _ f.bijective

-- lemma power_le_power_left' : ∀{a b c : cardinal.{u}}, b ≠ 0 → b ≤ c → a ^ b ≤ a ^ c :=
-- sorry

theorem le_mk_iff_exists_subset {c : cardinal} {α : Type u} {s : set α} :
  c ≤ mk s ↔ ∃ p : set α, p ⊆ s ∧ mk p = c :=
begin
  rw [le_mk_iff_exists_set, ←exists_set_subtype],
  apply exists_congr, intro t, rw [mk_image_eq], apply subtype.val_injective
end

lemma power_nat_le {c : cardinal.{u}} {n : ℕ} (h  : omega ≤ c) : c ^ (n : cardinal.{u}) ≤ c :=
begin
  induction n; unfold_coes; rw [nat.cast],
  { rw [power_zero], exact le_trans (le_of_lt one_lt_omega) h },
  rw [power_add, power_one, mul_comm],
  convert mul_le_max_of_omega_le_left h, rw [max_eq_left], exact n_ih
end

/-- The function α^{<β}, defined to be sup_{γ < β} α^γ.
  We index over {s : set β.out // mk s < β } instead of {γ // γ < β}, because the latter lives in a
  higher universe -/
def powerlt (α β : cardinal.{u}) : cardinal.{u} :=
-- @min.{u+1 u} {γ : cardinal // ∀ δ < β, α ^ δ ≤ γ}
--   ⟨⟨max (α ^ β) 1, λ δ hδ, _⟩⟩
--   subtype.val
sup.{u u} (λ(s : {s : set β.out // mk s < β}), α ^ mk.{u} s)

infix ` ^< `:80 := powerlt

def out_embedding {c c' : cardinal} (h : c ≤ c') : nonempty (c.out ↪ c'.out) :=
by rwa [←quotient.out_eq c, ←quotient.out_eq c'] at h

def powerlt_helper {c c' : cardinal} (h : c < c') :
  ∃(s : {s : set c'.out // mk s < c'}), mk s = c :=
begin
  cases out_embedding (le_of_lt h) with f,
  have : mk ↥(range ⇑f) = c, { rwa [mk_range_eq, mk, quotient.out_eq c], exact f.2 },
  exact ⟨⟨range f, by convert h⟩, this⟩
end

lemma le_powerlt {c₁ c₂ c₃ : cardinal} (h : c₂ < c₃) : c₁ ^ c₂ ≤ c₁ ^< c₃ :=
by { rcases powerlt_helper h with ⟨s, rfl⟩, apply le_sup _ s }

lemma powerlt_le {c₁ c₂ c₃ : cardinal} : c₁ ^< c₂ ≤ c₃ ↔ ∀(c₄ < c₂), c₁ ^ c₄ ≤ c₃ :=
begin
  rw [powerlt, sup_le],
  split,
  { intros h c₄ hc₄, rcases powerlt_helper hc₄ with ⟨s, rfl⟩, exact h s },
  intros h s, exact h _ s.2
end

lemma powerlt_omega {c : cardinal} (h : omega ≤ c) : c ^< omega = c :=
begin
  apply le_antisymm,
  { rw [powerlt_le], intro c', rw [lt_omega], rintro ⟨n, rfl⟩, apply power_nat_le h },
  convert le_powerlt one_lt_omega, rw [power_one]
end

lemma powerlt_omega_le (c : cardinal) : c ^< omega ≤ max c omega :=
begin
  cases le_or_gt omega c,
  { rw [powerlt_omega h], apply le_max_left },
  rw [powerlt_le], intros c' hc',
  refine le_trans (le_of_lt $ power_lt_omega h hc') (le_max_right _ _)
end

lemma powerlt_le_powerlt_left {a b c : cardinal} (h : b ≤ c) : a ^< b ≤ a ^< c :=
by { rw [powerlt, sup_le], rintro ⟨s, hs⟩, apply le_powerlt, exact lt_of_lt_of_le hs h }

-- lemma powerlt_eq (α β : Type u) :
--   powerlt (mk α) (mk β) = mk.{u} (Σ(s : {s : set β // mk s < mk β}), s → α) :=
-- begin

-- end
-- sup.{u u} (λ(s : {s : set β.out // mk s < β}), α ^ mk.{u} s)
-- quotient.lift_on₂ α β (λ γ δ, mk.{u} (Σ(s : {s : set δ // mk s < mk δ}), s → γ))
--   begin
--     rintro γ₁ δ₁ γ₂ δ₂ ⟨e₁⟩ ⟨e₂⟩, dsimp, refine quotient.sound ⟨_⟩,
--     refine (equiv.sigma_congr_left $ _).symm.trans _,
--     { exact {s : set δ₂ // mk s < mk δ₂} },
--     { refine (equiv.subtype_equiv_of_subtype $ equiv.set_congr e₂.symm).trans _,
--       apply equiv.subtype_congr, intro s,
--       convert iff.rfl using 2,
--       change mk s = mk (e₂ '' s), rw [mk_image_eq], exact e₂.bijective.1,
--       exact quotient.sound ⟨e₂⟩ },
--     apply equiv.sigma_congr_right, rintro ⟨s, hs⟩,
--     apply equiv.arrow_congr _ e₁,
--     dsimp [equiv.set_congr, equiv.subtype_congr, equiv.subtype_equiv_of_subtype, subtype.map],
--     symmetry, apply equiv.set.image, exact e₂.symm.bijective.1
--   end

-- lemma powerlt_le_powerlt_right {a b c : cardinal} : a ≤ b → a ^< c ≤ b ^< c :=
-- sorry

-- lemma powerlt_zero (a : cardinal) : a ^< 0 = 0 :=
-- sorry

lemma powerlt_succ {c₁ c₂ : cardinal} (h : c₁ ≠ 0) : c₁ ^< c₂.succ = c₁ ^ c₂ :=
begin
  apply le_antisymm,
  { rw powerlt_le, intros c₃ h2, apply power_le_power_left h, rwa [←lt_succ] },
  { apply le_powerlt, apply lt_succ_self }
end

lemma powerlt_max {c₁ c₂ c₃ : cardinal} : c₁ ^< max c₂ c₃ = max (c₁ ^< c₂) (c₁ ^< c₃) :=
by { cases le_total c₂ c₃; simp only [max_eq_left, max_eq_right, h, powerlt_le_powerlt_left] }

lemma zero_powerlt {a : cardinal} (h : a ≠ 0) : 0 ^< a = 1 :=
begin
  apply le_antisymm,
  { rw [powerlt_le], intros c hc, apply zero_power_le },
  convert le_powerlt (pos_iff_ne_zero.2 h), rw [power_zero]
end

-- lemma mk_bounded_set (α : Type u) (c : cardinal) :
--   mk {t : set α // mk t < c} ≤ mk α ^< max c omega :=
-- begin
--   have : ∀{c : cardinal}, omega ≤ c → mk {t : set α // mk t < c} ≤ mk α ^< c,
--   { clear c, intro c, refine quotient.induction_on c _, clear c,
--     intros β hβ, sorry

--    },
--   refine le_trans _ (this (le_max_right _ _)), apply mk_le_of_subproperty,
--   rintro t ⟨ht₁, ht₂⟩, exact ⟨ht₁, lt_of_lt_of_le ht₂ (le_max_left _ _)⟩
-- end

local attribute [instance] [priority 0] classical.prop_decidable
lemma mk_bounded_set_le_of_omega_le (α : Type u) (c : cardinal) (hα : omega ≤ mk α) :
  mk {t : set α // mk t ≤ c} ≤ mk α ^ c :=
begin
  refine le_trans _ (by rw [←add_one_eq hα]), refine quotient.induction_on c _, clear c, intro β,
  fapply mk_le_of_surjective,
  { intro f, refine ⟨sum.inl ⁻¹' range f, _⟩,
    refine le_trans (mk_preimage_of_injective _ _ (λ x y, sum.inl.inj)) _,
    apply mk_range_le },
  rintro ⟨s, ⟨g⟩⟩,
  refine ⟨λ y, if h : ∃(x : s), g x = y then sum.inl (classical.some h).val else sum.inr ⟨⟩, _⟩,
  apply subtype.eq, ext,
  split,
  { rintro ⟨y, h⟩, dsimp only at h, by_cases h' : ∃ (z : s), g z = y,
    { rw [dif_pos h'] at h, cases sum.inl.inj h, exact (classical.some h').2 },
    { rw [dif_neg h'] at h, cases h }},
  { intro h, have : ∃(z : s), g z = g ⟨x, h⟩, exact ⟨⟨x, h⟩, rfl⟩,
    refine ⟨g ⟨x, h⟩, _⟩, dsimp only, rw [dif_pos this], congr',
    suffices : classical.some this = ⟨x, h⟩, exact congr_arg subtype.val this,
    apply g.2, exact classical.some_spec this }
end

lemma mk_bounded_set_le (α : Type u) (c : cardinal) :
  mk {t : set α // mk t ≤ c} ≤ max (mk α) omega ^ c :=
begin
  transitivity mk {t : set (ulift.{u} nat ⊕ α) // mk t ≤ c},
  { refine ⟨embedding.subtype_map _ _⟩, apply embedding.image,
    refine ⟨sum.inr, _⟩, apply sum.inr.inj, intros s hs, exact le_trans (mk_image_le _ _) hs },
  refine le_trans
    (mk_bounded_set_le_of_omega_le (ulift.{u} nat ⊕ α) c (le_add_right omega (mk α))) _,
  rw [max_comm, ←add_eq_max]; refl
end

-- lemma mk_bounded_set (α : Type u) (c : cardinal) :
--   mk {t : set α // mk t < c} ≤ max (mk α) omega ^< c :=
-- begin
--   sorry
-- end

-- lemma mk_bounded_set_le (α : Type u) (c : cardinal) :
--   mk {t : set α // mk t ≤ c} ≤ max (mk α ^ c) (mk α ^< omega) :=
-- sorry


-- lemma mk_bounded_subset {α : Type u} (s : set α) (c : cardinal) :
--   mk {t : set α // t ⊆ s ∧ mk t < c} ≤ mk s ^< max c omega :=
-- begin
--   have : ∀{c : cardinal}, omega ≤ c → mk {t : set α // t ⊆ s ∧ mk t < c} ≤ mk s ^< c,
--   { clear c, intro c, refine quotient.induction_on c _, clear c,
--     intros α hα, sorry
--     -- transitivity mk ⋃(c' : {c' : cardinal // c' < c}), {t : set α | t ⊆ s ∧ mk t = c'},
--     -- apply le_of_eq, sorry,
--     -- rw [←lift_le.{u (u+1)}, lift_mk],
--     -- transitivity mk ⋃(c' : {c' : cardinal // c' < c}),
--     --   {t : set (ulift.{u+1} α) | t ⊆ ulift.up '' s ∧ mk t = lift.{u (u+1)} c'.1},
--     -- sorry,
--     -- refine le_trans mk_Union_le_sum_mk _,
--    },
--   refine le_trans _ (this (le_max_right _ _)), apply mk_le_of_subproperty,
--   rintro t ⟨ht₁, ht₂⟩, exact ⟨ht₁, lt_of_lt_of_le ht₂ (le_max_left _ _)⟩
-- end

lemma mk_bounded_subset_le {α : Type u} (s : set α) (c : cardinal) :
  mk {t : set α // t ⊆ s ∧ mk t ≤ c} ≤ max (mk s) omega ^ c :=
begin
  refine le_trans _ (mk_bounded_set_le s c),
  refine ⟨embedding.cod_restrict _ _ _⟩,
  refine ⟨λ t, subtype.val ⁻¹' t.1, _⟩,
  { rintros ⟨t, ht1, ht2⟩ ⟨t', h1t', h2t'⟩ h, apply subtype.eq, dsimp only at h ⊢,
    refine (preimage_eq_preimage' _ _).1 h; rw [range_val]; assumption },
  rintro ⟨t, h1t, h2t⟩, exact le_trans (mk_preimage_of_injective _ _ subtype.val_injective) h2t
end

-- begin
--   have := mk_bounded_subset s c.succ, simp only [lt_succ] at this,
--   apply le_trans this, rw [powerlt_max],
--   by_cases h : mk s = 0,
--   { rw [h, zero_powerlt omega_ne_zero, zero_powerlt (succ_ne_zero c), max_self, max_eq_right],
--     apply zero_power_le },
--   rw [powerlt_succ h]
-- end

end cardinal

namespace ordinal

open function
variables {α : Type u} {β : Type v} {γ : Type w}
local attribute [instance] [priority 0] classical.prop_decidable

lemma injective_typein (r : α → α → Prop) [is_well_order α r] : injective (typein r) :=
injective_of_increasing r (<) (typein r) (λ x y, (typein_lt_typein r).2)

def typesub (r : α → α → Prop) [is_well_order α r] (s : set α) : ordinal :=
type (subrel r s)

-- def strict_upper_bounds [has_lt α] (s : set α) : set α := { x | ∀a ∈ s, a < x }
-- def unbounded {α : Type u} [preorder α] (s : set α) : Prop := strict_upper_bounds s = ∅

@[simp] lemma not_bounded_iff {r : α → α → Prop} (s : set α) : ¬bounded r s ↔ unbounded r s :=
by simp only [bounded, unbounded, not_forall, not_exists, exists_prop, not_and, not_not]

@[simp] lemma not_unbounded_iff {r : α → α → Prop} (s : set α) : ¬unbounded r s ↔ bounded r s :=
by simp only [bounded, unbounded, not_forall, not_exists, exists_prop, not_and, not_not]

lemma type_out (o : ordinal) : type o.out.r = o :=
by { refine eq.trans _ (by rw [←quotient.out_eq o]), cases quotient.out o, refl }

noncomputable def initial_seg_out {α β : ordinal} (h : α ≤ β) : initial_seg α.out.r β.out.r :=
begin
  rw [←quotient.out_eq α, ←quotient.out_eq β] at h, revert h,
  cases quotient.out α, cases quotient.out β, exact classical.choice
end

noncomputable def principal_seg_out {α β : ordinal} (h : α < β) : principal_seg α.out.r β.out.r :=
begin
  rw [←quotient.out_eq α, ←quotient.out_eq β] at h, revert h,
  cases quotient.out α, cases quotient.out β, exact classical.choice
end

noncomputable def order_iso_out {α β : ordinal} (h : α = β) : order_iso α.out.r β.out.r :=
begin
  rw [←quotient.out_eq α, ←quotient.out_eq β] at h, revert h,
  cases quotient.out α, cases quotient.out β, exact classical.choice ∘ quotient.exact
end

lemma has_succ_of_is_limit {α} {r : α → α → Prop} [wo : is_well_order α r]
  (h : (type r).is_limit) (x : α) : ∃y, r x y :=
let z : ordinal := typein r x in
let sz : ordinal := z.succ in
have sz_lt : sz < type r, from h.2 _ $ typein_lt_type r x,
let ⟨y, hy⟩ := typein_surj r sz_lt in
⟨y, (typein_lt_typein r).mp (by {rw [hy], apply lt_succ_self})⟩

lemma sup_succ {ι} (f : ι → ordinal) : sup (λ i, succ (f i)) ≤ succ (sup f) :=
by { rw [ordinal.sup_le], intro i, rw ordinal.succ_le_succ, apply ordinal.le_sup }

-- lemma typein_succ {α} {r : α → α → Prop} [wo : is_well_order α r] (x : α) (h : ∃y, r x y) :
--   typein r (wo.wf.succ x h) = (typein r x).succ :=
-- quotient.sound $ sorry

namespace order_iso

  @[simp] lemma to_equiv_to_fun {r : α → α → Prop} {s : β → β → Prop} (f : r ≃o s) (x : α) :
    f.to_equiv.to_fun x = f x :=
  rfl

  lemma ord'' {r : α → α → Prop} {s : β → β → Prop} (f : r ≃o s) {x y : α} :
    r x y ↔ s ((f : r ≼o s) x) ((↑f : r ≼o s) y) :=
  f.ord'

end order_iso

namespace principal_seg

def lt_equiv {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
  [is_trans β s] [is_trans γ t] (f : principal_seg r s) (g : s ≃o t) : principal_seg r t :=
⟨@order_embedding.trans _ _ _ r s t f g, g f.top,
  begin
    intro x,
    rw [←g.right_inv x],
    simp only [ordinal.order_iso.to_equiv_to_fun, coe_fn_coe_base, order_embedding.trans_apply],
    rw [←order_iso.ord'' g, f.down', exists_congr],
    intro y, exact ⟨congr_arg g, λ h, g.to_equiv.bijective.1 h⟩
  end⟩

end principal_seg

def nth (r : α → α → Prop) [is_well_order α r] (o : {x // x < type r}) : α :=
begin
  cases o with o h, induction o,
  { rcases o with ⟨β, s, wo⟩, exact (classical.choice h).top },
  rcases o_a with ⟨β, s, wo⟩, rcases o_b with ⟨β', s', wo'⟩, resetI,
  cases p with f, apply eq_of_heq, apply rec_heq_of_heq,
  apply function.hfunext, { congr' 1, apply quot.sound, constructor, exact f },
  intros h h' _, apply heq_of_eq, exact principal_seg.top_eq f _ _
end

def nth_type {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s]
  (h : nonempty (principal_seg s r)) : nth r ⟨type s, h⟩ = (classical.choice h).top :=
by refl

lemma top_lt_top {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
  [is_trans β s] [is_well_order γ t]
  (f : principal_seg r s) (g : principal_seg s t) (h : principal_seg r t) : t h.top g.top :=
by { rw [subsingleton.elim h (f.trans g)], apply principal_seg.lt_top }

lemma order_iso_nth' {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s]
  (f : order_iso r s) (o : ordinal) : ∀(hr : o < type r) (hs : o < type s),
  f (nth r ⟨o, hr⟩) = nth s ⟨o, hs⟩ :=
begin
  refine induction_on o _,
  rintros γ t wo ⟨g⟩ ⟨h⟩,
  simp [nth_type], symmetry,
  rw [subsingleton.elim (classical.choice ⟨h⟩)
      (principal_seg.lt_equiv (classical.choice ⟨g⟩) f)],
  refl
end

lemma order_iso_nth {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s]
  (f : order_iso r s) (o : ordinal) (hr : o < type r) :
  f (nth r ⟨o, hr⟩) =
  nth s ⟨o, by {convert hr using 1, apply quotient.sound, exact ⟨f.symm⟩ }⟩ :=
order_iso_nth' _ _ _ _

@[simp] lemma typein_nth (r : α → α → Prop) [is_well_order α r] : ∀(o : {x // x < type r}),
  typein r (nth r o) = o
| ⟨o, h⟩ := induction_on o (λ β s _ ⟨f⟩, by exactI typein_top _) h

@[simp] lemma nth_typein (r : α → α → Prop) [is_well_order α r] (x : α) :
  nth r ⟨typein r x, typein_lt_type r x⟩ = x :=
begin
  rw [←principal_seg.of_element_top r x], exact congr_arg principal_seg.top (subsingleton.elim _ _)
end

def typein_iso (r : α → α → Prop) [is_well_order α r] : r ≃o subrel (<) (< type r) :=
⟨⟨λ x, ⟨typein r x, typein_lt_type r x⟩, nth r, nth_typein r, λ y, subtype.eq (typein_nth r y)⟩,
  λ a b, (typein_lt_typein r).symm⟩

lemma nth_lt_nth (r : α → α → Prop) [is_well_order α r] {o o' : {x // x < type r}} :
  o.1 < o'.1 ↔ r (nth r o) (nth r o') :=
begin
  rw [(typein_iso r).ord], dsimp [subrel, typein_iso], rw [typein_nth, typein_nth], refl
end

lemma le_iff_not_gt [linear_order α] (x y : α) : x ≤ y ↔ ¬x > y :=
⟨not_lt_of_ge, le_of_not_gt⟩

@[simp] lemma typein_le_typein (r : α → α → Prop) [is_well_order α r] {x x' : α} :
  typein r x ≤ typein r x' ↔ ¬r x' x :=
by rw [le_iff_not_gt, not_iff_not, gt, typein_lt_typein]

lemma nth_le_nth (r : α → α → Prop) [is_well_order α r] {o o' : {x // x < type r}} :
  ¬r (nth r o') (nth r o) ↔ o.1 ≤ o'.1 :=
by rw [le_iff_not_gt, not_iff_not, gt, nth_lt_nth]

lemma type_subrel (r : α → α → Prop) [is_well_order α r] (x : α) :
  type (subrel r {y | r y x}) = typein r x :=
rfl

lemma unbounded_range_of_sup_ge {β} (r : α → α → Prop) [is_well_order α r] (f : β → α)
  (h : sup.{u u} (typein r ∘ f) ≥ type r) : unbounded r (range f) :=
begin
  apply (not_bounded_iff _).mp, rintro ⟨x, hx⟩, apply not_lt_of_ge h,
  refine lt_of_le_of_lt _ (typein_lt_type r x), rw [sup_le], intro y,
  apply le_of_lt, rw typein_lt_typein, apply hx, apply mem_range_self
end

-- lemma unbounded_range_iff_sup_eq {β} (r : α → α → Prop) [is_well_order α r] (f : β → α) :
--   unbounded r (range f) ↔ sup.{u u} (typein r ∘ f) = type r :=
-- begin
--   split, intro h, apply le_antisymm, sorry, sorry,
--   intro h, apply unbounded_range_of_sup_ge, apply le_of_eq, exact h.symm
-- end

-- lemma sup_typein_iff (r : α → α → Prop) [is_well_order α r] (f : ι → ordinal) :
--   sup

open cardinal

lemma ord_injective : injective ord :=
by { intros c c' h, rw [←card_ord c, ←card_ord c', h] }

lemma card_typein_lt (r : α → α → Prop) [is_well_order α r] (x : α)
  (h : ord (mk α) = type r) : card (typein r x) < mk α :=
by { rw [←ord_lt_ord, h], refine lt_of_le_of_lt (ord_card_le _) (typein_lt_type r x) }

lemma mk_ord_out (c : cardinal) : mk c.ord.out.α = c :=
by rw [←card_type c.ord.out.r, type_out, card_ord]

lemma card_typein_out_lt (c : cardinal) (x : c.ord.out.α) : card (typein c.ord.out.r x) < c :=
by { convert card_typein_lt c.ord.out.r x _, rw [mk_ord_out], rw [type_out, mk_ord_out] }

lemma type_subrel_lt (o : ordinal.{u}) :
  type (subrel (<) {o' : ordinal | o' < o}) = ordinal.lift.{u u+1} o :=
begin
  refine quotient.induction_on o _,
  rintro ⟨α, r, wo⟩, resetI, apply quotient.sound,
  constructor, symmetry, refine (order_iso.preimage equiv.ulift r).trans (typein_iso r)
end

lemma mk_initial_seg (o : ordinal.{u}) :
  mk {o' : ordinal | o' < o} = cardinal.lift.{u u+1} o.card :=
by rw [lift_card, ←type_subrel_lt, card_type]

namespace order
lemma cof_le (r : α → α → Prop) [is_refl α r] {S : set α} (h : ∀a, ∃(b ∈ S), r a b) :
  order.cof r ≤ mk S :=
le_trans (cardinal.min_le _ ⟨S, h⟩) (le_refl _)

lemma le_cof {r : α → α → Prop} [is_refl α r] (c : cardinal) :
  c ≤ order.cof r ↔ ∀ {S : set α} (h : ∀a, ∃(b ∈ S), r a b) , c ≤ mk S :=
by { rw [order.cof, cardinal.le_min], exact ⟨λ H S h, H ⟨S, h⟩, λ H ⟨S, h⟩, H h ⟩ }

end order

-- theorem bsup_lt_of_is_regular (o : ordinal.{u}) (f : Π a < o, ordinal.{u})
--   {c} (hc : is_regular c) (H1 : o < c.ord)
--   (H2 : ∀a < o, f a H < c.ord) : bsup.{u u} o f < c.ord :=
-- sorry

def strict_order.cof (r : α → α → Prop) [h : is_irrefl α r] : cardinal :=
@order.cof α (λ x y, ¬ r y x) ⟨h.1⟩

lemma cof_type (r : α → α → Prop) [is_well_order α r] : (type r).cof = strict_order.cof r :=
rfl

lemma lt_ord_succ_card (o : ordinal) : o < o.card.succ.ord :=
by { rw [lt_ord], apply cardinal.lt_succ_self }

lemma typein_card_eq {r : α → α → Prop} [wo : is_well_order α r] (x : α) :
  mk {y // r y x} = (typein r x).card :=
rfl

/- cofinality -/
lemma cof_type_eq {r : α → α → Prop} [wo : is_well_order α r] : strict_order.cof r = cof (type r) :=
by refl

theorem sup_lt_ord {ι} (f : ι → ordinal) {c : cardinal} (H1 : cardinal.mk ι < c.ord.cof)
  (H2 : ∀ i, f i < c.ord) : sup.{u u} f < c.ord :=
begin
  apply lt_of_le_of_ne,
  rw [sup_le], exact λ i, le_of_lt (H2 i),
  rintro h, apply not_le_of_lt H1,
  simpa [sup_ord, H2, h] using cof_sup_le.{u} f
end

theorem sup_lt {ι} (f : ι → cardinal) {c : cardinal} (H1 : cardinal.mk ι < c.ord.cof)
  (H2 : ∀ i, f i < c) : cardinal.sup.{u u} f < c :=
by { rw [←ord_lt_ord, ←sup_ord], apply sup_lt_ord _ H1, intro i, rw ord_lt_ord, apply H2 }

theorem sup_lt_ord_of_is_regular {ι} (f : ι → ordinal)
  {c} (hc : is_regular c) (H1 : cardinal.mk ι < c)
  (H2 : ∀ i, f i < c.ord) : sup.{u u} f < c.ord :=
by { apply sup_lt_ord _ _ H2, rw [hc.2], exact H1 }

/-- If the union of s is unbounded and s is smaller than the cofinality, then s has an unbounded member -/
theorem unbounded_of_unbounded_sUnion (r : α → α → Prop) [wo : is_well_order α r] {s : set (set α)}
  (h₁ : unbounded r $ ⋃₀ s) (h₂ : mk s < strict_order.cof r) : ∃(x ∈ s), unbounded r x :=
begin
  by_contra h, simp only [not_exists, exists_prop, not_and, not_unbounded_iff] at h,
  apply not_le_of_lt h₂,
  let f : s → α := λ x : s, wo.wf.sup x (h x.1 x.2),
  let t : set α := range f,
  have : mk t ≤ mk s, exact mk_range_le _, refine le_trans _ this,
  have : unbounded r t,
  { intro x, rcases h₁ x with ⟨y, ⟨c, hc, hy⟩, hxy⟩,
    refine ⟨f ⟨c, hc⟩, mem_range_self _, _⟩, intro hxz, apply hxy,
    refine trans (wo.wf.lt_sup _ hy) hxz },
  exact cardinal.min_le _ (subtype.mk t this)
end

/-- If the union of s is unbounded and s is smaller than the cofinality, then s has an unbounded member -/
theorem unbounded_of_unbounded_Union {α β : Type u} (r : α → α → Prop) [wo : is_well_order α r]
  (s : β → set α)
  (h₁ : unbounded r $ ⋃x, s x) (h₂ : mk β < strict_order.cof r) : ∃x : β, unbounded r (s x) :=
begin
  rw [Union_eq_sUnion_range] at h₁,
  have : mk ↥(range (λ (i : β), s i)) < strict_order.cof r := lt_of_le_of_lt (mk_range_le _) h₂,
  rcases unbounded_of_unbounded_sUnion r h₁ this with ⟨_, ⟨x, rfl⟩, u⟩, exact ⟨x, u⟩
end

/-- The infinite pigeonhole principle-/
theorem infinite_pigeonhole {β α : Type u} (f : β → α) (h₁ : cardinal.omega ≤ mk β)
  (h₂ : mk α < (mk β).ord.cof) : ∃a : α, mk (f ⁻¹' {a}) = mk β :=
begin
  have : ¬∀a, mk (f ⁻¹' {a}) < mk β,
  { intro h,
    apply not_lt_of_ge (ge_of_eq $ mk_univ β),
    rw [←@preimage_univ _ _ f, ←Union_of_singleton, preimage_Union],
    apply lt_of_le_of_lt mk_Union_le_sum_mk,
    apply lt_of_le_of_lt (sum_le_sup _),
    apply mul_lt_of_lt h₁ (lt_of_lt_of_le h₂ $ cof_ord_le _),
    exact sup_lt _ h₂ h },
  rw [not_forall] at this, cases this with x h,
  refine ⟨x, _⟩, apply le_antisymm _ (le_of_not_gt h),
  rw [le_mk_iff_exists_set], exact ⟨_, rfl⟩
end

/-- pigeonhole principle for a cardinality below the cardinality of the domain -/
theorem infinite_pigeonhole_card {β α : Type u} (f : β → α) (θ : cardinal) (hθ : θ ≤ mk β)
  (h₁ : cardinal.omega ≤ θ) (h₂ : mk α < θ.ord.cof) : ∃a : α, θ ≤ mk (f ⁻¹' {a}) :=
begin
  rcases le_mk_iff_exists_set.1 hθ with ⟨s, rfl⟩,
  cases infinite_pigeonhole (f ∘ subtype.val : s → α) h₁ h₂ with a ha,
  refine ⟨a, _⟩, rw [←ha, @preimage_comp _ _ _ subtype.val f],
  apply mk_preimage_of_injective _ _ subtype.val_injective
end

theorem infinite_pigeonhole_set {β α : Type u} {s : set β} (f : s → α) (θ : cardinal) (hθ : θ ≤ mk s)
  (h₁ : cardinal.omega ≤ θ) (h₂ : mk α < θ.ord.cof) :
    ∃(a : α) (t : set β) (h : t ⊆ s), θ ≤ mk t ∧ ∀{{x}} (hx : x ∈ t), f ⟨x, h hx⟩ = a :=
begin
  cases infinite_pigeonhole_card f θ hθ h₁ h₂ with a ha,
  refine ⟨a, {x | ∃(h : x ∈ s), f ⟨x, h⟩ = a}, _, _, _⟩,
  { rintro x ⟨hx, hx'⟩, exact hx },
  { refine le_trans ha _, apply ge_of_eq, apply quotient.sound, constructor,
    refine equiv.trans _ (equiv.subtype_subtype_equiv_subtype _ _).symm,
    simp only [set_coe_eq_subtype, mem_singleton_iff, mem_preimage_eq, mem_set_of_eq] },
  rintro x ⟨hx, hx'⟩, exact hx'
end


end ordinal
open ordinal

def is_delta_system {α : Type u} (A : set (set α)) :=
∃(root : set α), ∀{{x y}}, x ∈ A → y ∈ A → x ≠ y → x ∩ y = root

open function
lemma is_delta_system_image {α β : Type*} {A : set (set α)} {f : α → β} (hf : injective f)
  (h : is_delta_system A) : is_delta_system (image f '' A) :=
begin
  cases h with r hr,
  refine ⟨f '' r, _⟩,
  rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ hxy,
  rw [image_inter hf], apply congr_arg (image f), apply hr hx hy, intro hxy', apply hxy, rw hxy'
end

lemma is_delta_system_preimage {α β : Type*} {A : set (set α)} {f : β → α}
  (h : is_delta_system A) : is_delta_system (preimage f '' A) :=
begin
  cases h with r hr,
  refine ⟨f ⁻¹' r, _⟩,
  rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ hxy,
  rw [←preimage_inter], apply congr_arg (preimage f), apply hr hx hy, intro hxy', apply hxy, rw hxy'
end



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
  {A : set (set θ)} (hA2 : ∀{s : set θ} (h : s ∈ A), ρr ≃o subrel θr s)
  (hA3 : unbounded θr (⋃₀ A)) : ∃(B ⊆ A), mk B = mk θ ∧ is_delta_system B :=
begin
  haveI := decidable_linear_order_of_is_well_order θr,
  let ι : θ → ordinal := typein θr,
  let nr : A → ρ → θ := λ s ξ, (hA2 s.2 ξ).val,
  let good : ρ → Prop := λ ξ, unbounded θr (range $ λ x, nr x ξ),
  have : ∃ξ : ρ, good ξ,
  { apply unbounded_of_unbounded_Union θr (λ ξ, range $ λ x, nr x ξ),
    { rw [Union_range_eq_sUnion], exact hA3, intro s, exact (hA2 s.2).to_equiv.bijective.2 },
    { rw [cof_type_eq, ←θtype_eq, hθ.2], refine lt_trans hρ hκθ }},
  let ξ₀ : ρ := ρwo.wf.min good (ne_empty_of_exists_mem this),
  let α₀ : ordinal := sup.{u u} (λ o : {x // ρr x ξ₀}, sup.{u u} $ λ s : A,
    ordinal.succ $ ι $ nr s o.1),
  have hα₀ : α₀ < type θr ,
  { rw [←θtype_eq], apply sup_lt_ord_of_is_regular _ hθ,
    { refine lt_of_le_of_lt _ (lt_trans hρ hκθ), rw [typein_card_eq, ←card_type ρr],
    apply card_le_card, apply le_of_lt, apply typein_lt_type },
    rintro ⟨ξ, hξ⟩, refine lt_of_le_of_lt (sup_succ _) _,
    apply (ord_is_limit hθ.1).2, apply lt_of_not_ge, intro h,
    apply ρwo.wf.not_lt_min _ _ _ hξ, apply unbounded_range_of_sup_ge,
    dsimp, rw [←θtype_eq], exact h },
  let pick' : ∀(μ : θ), ∀(pick : ∀y, θr y μ → A), ordinal :=
  λ μ pick, max α₀ $ sup.{u u} (λ x : ρ × {x // θr x μ}, ι $ nr (pick x.2.val x.2.2) x.1),
  have pick'_lt : ∀(μ : θ) (pick : ∀y, θr y μ → A), pick' μ pick < type θr,
  { intros μ pick,
    apply max_lt hα₀,
    rw [←θtype_eq],
    apply sup_lt_ord_of_is_regular _ hθ,
    { apply @mul_lt_of_lt (mk ρ) (mk {x // θr x μ}) _ hθ.1 (lt_trans hρ hκθ),
      rw [←ord_lt_ord, θtype_eq], apply lt_of_le_of_lt (ord_le_type (subrel θr {x | θr x μ})),
      apply typein_lt_type },
    rintro ⟨x, y, hy⟩, rw [θtype_eq], apply typein_lt_type },
  have : ∀(x : θ), ∃s : A, θr x (nr s ξ₀),
  { intro x, have : good ξ₀ := ρwo.wf.min_mem good _,
    have θr_unbounded : ∀(x : θ), ∃y, θr x y,
    { intro y, apply has_succ_of_is_limit, rw [←θtype_eq], exact ord_is_limit hθ.1 },
    cases θr_unbounded x with y hy,
    rcases this y with ⟨z, ⟨s, rfl⟩, hz⟩,
    refine ⟨s, _⟩, rcases trichotomous_of θr (nr s ξ₀) y with hw | rfl | hw,
    exfalso, exact hz hw, exact hy, exact trans hy hw },
  let pick : θ → A := θwo.wf.fix
    (λ μ pick, classical.some $ this $ nth θr $ ⟨pick' μ pick, pick'_lt μ pick⟩),
  have lt_pick : ∀(μ : θ),
    θr (nth θr $ ⟨pick' μ (λ y _, pick y), pick'_lt μ (λ y _, pick y)⟩) (nr (pick μ) ξ₀),
  { intro μ, dsimp [pick], rw [θwo.wf.fix_eq _ μ], apply classical.some_spec (this _) },
  have pick_lt_pick : ∀{μ ν : θ} (h : θr ν μ) (η : ρ),
    θr (nr (pick ν) η) (nr (pick μ) ξ₀),
  { intros, apply trans_trichotomous_left _ (lt_pick μ), rw [←typein_le_typein, typein_nth],
    refine le_trans _ (le_max_right _ _), refine le_trans _ (le_sup _ ⟨η, ν, h⟩), refl },
  let A2 := range (subtype.val ∘ pick),
  have h1A2 : mk A2 = mk θ,
  { have increasing_pick : ∀{{x y : θ}}, θr x y → θr (nr (pick x) ξ₀) (nr (pick y) ξ₀),
    { intros x y hxy, apply pick_lt_pick hxy ξ₀ },
    have injective_pick : injective pick,
    { intros x y hx, apply injective_of_increasing _ _ _ increasing_pick, dsimp only,
      congr' 1, exact hx },
    rw [mk_range_eq], apply injective_comp, exact subtype.val_injective, apply injective_pick },
  let sub_α₀ : set θ := ι ⁻¹' {c | c < α₀},
  have h1sub_α₀ : mk ↥sub_α₀ = α₀.card,
  { rw [←cardinal.lift_inj.{_ u+1}, mk_preimage_of_injective_of_onto_lift],
    rw [mk_initial_seg, cardinal.lift_lift],
    exact injective_typein θr,
    intros o ho,
    rcases typein_surj θr (lt_trans ho hα₀) with ⟨_, rfl⟩,
    apply mem_range_self },
  have h2A2' : ∀{x y : θ}, θr x y → (pick x).val ∩ (pick y).val ⊆ sub_α₀,
  { rintros x y hxy z ⟨hzx, hzy⟩,
    let η := typein (subrel θr (pick y)) ⟨z, hzy⟩,
    have η_def : z = (nth (subrel θr (pick y)) ⟨η, typein_lt_type _ _⟩).val, { rw [nth_typein] },
    cases lt_or_ge η (typein ρr ξ₀) with h h,
    { rw [mem_preimage_eq, mem_set_of_eq],
      refine lt_of_lt_of_le _ (ordinal.le_sup _ _),
      { refine ⟨nth ρr ⟨η, lt_trans h (typein_lt_type _ _)⟩, _⟩,
        rw [←typein_lt_typein ρr, typein_nth], exact h },
      refine lt_of_lt_of_le _ (ordinal.le_sup _ (pick y)),
      convert lt_succ_self (ι z), rw [η_def],
      dsimp [nr], congr' 1, apply order_iso_nth' (hA2 _) },
    exfalso,
    have η_lt : η < type ρr,
    { convert typein_lt_type (subrel θr (pick y)) ⟨z, hzy⟩ using 1, apply quotient.sound,
      exact ⟨hA2 (pick y).2⟩ },
    have : ¬ρr (nth ρr ⟨η, η_lt⟩) ξ₀, { rw [←typein_le_typein, typein_nth], exact h },
    apply this,
    rw [(hA2 (pick y).2).ord], dsimp only [subrel, order.preimage],
    convert pick_lt_pick hxy ((hA2 (pick x).2).symm ⟨z, hzx⟩) using 1,
    transitivity z, { rw [η_def], congr' 1, apply order_iso_nth (hA2 _) },
    transitivity subtype.val ⟨z, hzx⟩, refl,
    congr' 1, symmetry, apply equiv.right_inv },
  have h2A2 : ∀(x ∈ A2) (y ∈ A2), x ≠ y → x ∩ y ⊆ sub_α₀,
  { rintros _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy,
    rcases trichotomous_of θr x y with h | h | h,
    apply h2A2' h,
    exfalso, apply hxy, rw h,
    rw [inter_comm], apply h2A2' h },
  let codomain := {s : set θ // s ⊆ sub_α₀ ∧ mk s ≤ mk ρ},
  have hsub_α₀ : mk ↥sub_α₀ < mk θ,
  { rw [h1sub_α₀, ←ord_lt_ord, θtype_eq], refine lt_of_le_of_lt (ord_card_le _) hα₀ },
  have hcodomain : ∀(s : A2), s.val ∩ sub_α₀ ⊆ sub_α₀ ∧ mk (↥(s.val ∩ sub_α₀)) ≤ mk ρ,
  { have α₀_lt_pick : ∀(μ : θ), θr (nth θr ⟨α₀, hα₀⟩) (nr (pick μ) ξ₀),
    { intro μ, apply trans_trichotomous_left _ (lt_pick μ), rw nth_le_nth, apply le_max_left },
    rintro ⟨s, hs⟩, refine ⟨inter_subset_right _ _, _⟩,
    rcases hs with ⟨μ, rfl⟩, dsimp,
    transitivity mk {x : (pick μ).val // ι x.1 < α₀},
    { apply le_of_eq, apply quotient.sound, constructor,
      symmetry, refine (equiv.subtype_subtype_equiv_subtype _ _).trans _, simp only [exists_prop] },
    let f := (hA2 (pick μ).2).to_equiv,
    rw [mk_subtype_of_equiv _ f.symm],
    transitivity mk { x : ρ // ρr x ξ₀},
    { apply mk_le_of_subproperty, intros x hx,
      rw [(hA2 (pick μ).2).ord], dsimp only [subrel, order.preimage],
      refine trans _ (α₀_lt_pick μ),
      rw [←nth_typein θr (f x).val, ←nth_lt_nth θr], exact hx },
    transitivity (typein ρr ξ₀).card, { rw [typein, card_type], refl },
    rw [←card_type ρr], apply card_le_card, apply le_of_lt, apply typein_lt_type },
  let f : A2 → codomain := λs, ⟨s.val ∩ sub_α₀, hcodomain s⟩,
  have : ∃r B, r ⊆ sub_α₀ ∧ B ⊆ A2 ∧ mk B = mk θ ∧ ∀(x ∈ B), x ∩ sub_α₀ = r,
  { have h1 : cardinal.omega ≤ mk ↥A2, { rw [h1A2], exact hθ.1 },
    have h2 : mk codomain < cof (ord (mk ↥A2)),
    { rw [h1A2, hθ.2],
      apply lt_of_le_of_lt (mk_bounded_subset_le _ _),
      refine lt_of_le_of_lt (le_powerlt hρ) (hθ_le _ _),
      apply max_lt hsub_α₀ (lt_of_le_of_lt hκ hκθ) },
    cases infinite_pigeonhole f h1 h2 with r' hr',
    refine ⟨r'.val, subtype.val '' (f ⁻¹' {r'}), _, _, _, _⟩,
    { rintro x hx, exact r'.2.1 hx },
    { rintro _ ⟨⟨x, hx⟩, _, rfl⟩, exact hx },
    { rw [mk_image_eq _ _ subtype.val_injective, ←h1A2, ←hr'] },
    { rintro _ ⟨⟨x, hx⟩, hx', rfl⟩,
      simpa only [set.mem_singleton_iff, set.mem_preimage_eq, f, subtype.ext] using hx' }},
  rcases this with ⟨r, B, hr, h1B, h2B, h3B⟩,
  refine ⟨B, subset.trans h1B _, h2B, r, _⟩, rw [range_subset_iff], intro x, exact (pick x).2,
  intros x y hx hy hxy, rw [←h3B x hx], apply set.ext, intro z, split,
  intro hz, refine ⟨hz.1, h2A2 x (h1B hx) y (h1B hy) hxy hz⟩,
  intro hz, refine ⟨hz.1, _⟩, rw [h3B x hx, ←h3B y hy] at hz, exact hz.1
end

/-- The delta-system lemma. [Kunen 1980, Theorem 1.6, p49] -/
theorem delta_system_lemma {α : Type u} {κ : cardinal} (hκ : cardinal.omega ≤ κ) {θ} (hκθ : κ < θ)
  (hθ : is_regular θ) (hθ_le : ∀(c < θ), c ^< κ < θ) (A : set (set α))
  (hA : θ ≤ mk A) (h2A : ∀{s : set α} (h : s ∈ A), mk s < κ) :
  ∃(B ⊆ A), mk B = θ ∧ is_delta_system B :=
begin
  revert hθ hθ_le hκ hκθ hA h2A, refine quotient.induction_on θ _, clear θ,
  intros θ hθ hθ_le hκ hκθ hA h2A, rcases ord_eq θ with ⟨θr, θwo, θtype_eq⟩,
  rcases le_mk_iff_exists_subset.mp hA with ⟨A', hA'A, hA'⟩,
  have h2A' : ∀{s : set α} (h : s ∈ A'), mk s < κ := (λ s hs, h2A (hA'A hs)),
  resetI,
  let β := ⋃₀ A',
  have hβ : mk β ≤ mk θ,
  { refine le_trans (mk_sUnion _) _, rw [hA'],
    refine le_trans (mul_le_max_of_omega_le_left _) _, exact hθ.1,
    apply max_le, refl, rw [cardinal.sup_le],
    intro s, apply le_of_lt, apply lt_trans (h2A' s.2) hκθ },
  have h2β : A' ⊆ powerset (range (subtype.val : β → α)),
  { intros s hs x hx, refine ⟨⟨x, ⟨s, hs, hx⟩⟩, rfl⟩ },
  have f : β ↪ θ, { exact (classical.choice hβ) },
  let A₀ : set (set θ) := image f ∘ preimage subtype.val '' A',
  have hA₀ : mk θ ≤ mk A₀,
  { rw [mk_image_eq_of_inj_on, hA'], refl,
    apply inj_on_comp_of_injective_left (injective_image f.2),
    apply inj_on_preimage h2β },
  let κα := κ.ord.out.α,
  let κr := κ.ord.out.r,
  have h3A₀ : ∀(s : A₀), type (subrel θr ↑s) < type κr,
  { rintro ⟨t, ht⟩, rw [type_out, lt_ord, card_type], change mk t < κ,
    rcases ht with ⟨s, hs, rfl⟩,
    rw [mk_image_eq], rw [mk_preimage_of_injective_of_onto], apply h2A' hs,
    apply subtype.val_injective, apply h2β hs, exact f.2 },
  have hκθ' : mk κα < cof (ord (mk θ)),
  { rw [←card_type κr, type_out, card_ord], convert hκθ, exact hθ.2 },
  let g : A₀ → κα := λ s : A₀, nth κr ⟨type (subrel θr s), h3A₀ s⟩,
  rcases infinite_pigeonhole_set g (mk θ) hA₀ hθ.1 hκθ' with ⟨ρ', A₁, hA₁, h2A₁, h3A₁⟩,
  let ρ := { x : κα | x < ρ' },
  let ρr := subrel κr ρ,
  have hρ : mk ρ < κ, { exact card_typein_out_lt κ ρ', },
  have h4A₁ : Π(s ∈ A₁), ρr ≃o subrel θr s,
  { intros s hs, symmetry,
    have : type (subrel θr s) = typein κr ρ', { rw [← h3A₁ hs, typein_nth], refl },
    exact classical.choice (quotient.exact this) },
  have h5A₁ : unbounded θr (⋃₀ A₁),
  { rw [←not_bounded_iff], rintro ⟨x, hx⟩, apply not_lt_of_ge h2A₁,
    refine lt_of_le_of_lt _ (hθ_le (max (typein θr x).card omega) _),
    have := mk_bounded_subset_le {y | θr y x} (typein κr ρ').card,
    refine le_trans (le_trans _ this) _,
    { apply mk_le_of_subset, intros s hs, split, intros y hy, exact hx y ⟨s, hs, hy⟩,
      rw [←h3A₁ hs, typein_nth], refl },
    apply le_powerlt, exact hρ,
    apply max_lt,
    apply card_typein_lt θr x θtype_eq, apply lt_of_le_of_lt hκ hκθ },
  rcases delta_system_lemma_2 hκ θr hκθ hθ θtype_eq hθ_le ρr hρ h4A₁ h5A₁ with ⟨B, h1B, h2B, h3B⟩,
  refine ⟨image subtype.val ∘ preimage f '' B, _, _, _⟩,
  { rw [image_subset_iff], refine subset.trans h1B (subset.trans hA₁ _),
    rw [←image_subset_iff, ←image_comp], convert hA'A,
    convert image_eq_image_of_eq_on _, symmetry, apply image_id,
    intros s hs, dsimp only [function.comp],
    rw [preimage_image_eq], apply image_preimage_eq_of_subset, apply h2β hs, exact f.2 },
  { rw [mk_image_eq_of_inj_on], exact h2B,
    apply inj_on_comp_of_injective_left (injective_image subtype.val_injective),
    apply inj_on_preimage,
    intros s hs, rcases hA₁ (h1B hs) with ⟨t, ht, rfl⟩, apply image_subset_range },
  rw [image_comp], apply is_delta_system_image subtype.val_injective,
  apply is_delta_system_preimage h3B
end

theorem delta_system_lemma_countable {α} (A : set (finset α)) (h : cardinal.omega < mk A) :
  ∃(B ⊆ A), cardinal.omega < mk B ∧ is_delta_system (finset.to_set '' B) :=
begin
  have :  ∀ (c : cardinal), c < succ omega → c ^< omega < succ omega,
  { intros c hc, refine lt_of_le_of_lt (powerlt_omega_le _) _,
    apply max_lt hc (lt_succ_self _) },
  rcases delta_system_lemma (le_refl _) (lt_succ_self _) (succ_is_regular (le_refl _)) this
    (finset.to_set '' A) _ _ with ⟨B', h1B', h2B', h3B'⟩,
  rcases subset_image_iff.mp h1B' with ⟨B, HB, rfl⟩,
  refine ⟨B, HB, _, h3B'⟩,
  { rw [mk_image_eq] at h2B', rw [h2B'], apply cardinal.lt_succ_self,
    apply finset.to_set_injective },
  { rw [mk_image_eq, cardinal.succ_le], exact h, apply finset.to_set_injective },
  rintro _ ⟨s, hs, rfl⟩, apply finset_card_lt_omega
end

end delta_system

namespace topological_space

variables {α : Type u} [topological_space α]

def open_set (α : Type u) [topological_space α] : Type u := subtype (@_root_.is_open α _)

def countable_chain_condition : Prop :=
∀(s : set $ open_set α), pairwise (disjoint on s) → s.countable



end topological_space
