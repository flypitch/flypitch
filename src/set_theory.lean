import .to_mathlib topology.continuity

/-
note: in comment above cofinality, change sentence with
+  `∀ a, ∃ b ∈ S, ¬(b > a)`. It is defined for all ordinals, but
-/

universe variables u v w w'
noncomputable theory

section subtype
open function subtype

def restrict {α} {β : α → Type*} (f : ∀x, β x) (s : set α) (x : s) : β x.1 :=
f x.1

lemma restrict_apply {α} {β : α → Type*} (f : ∀x, β x) (s : set α) (x : s) :
  restrict f s x = f x.1 :=
by refl

lemma restrict_def {α β} (f : α → β) (s : set α) : restrict f s = f ∘ subtype.val :=
by refl

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

lemma exists_two_elements (h : (2 : cardinal) ≤ mk α) : ∃x y : α, x ≠ y :=
by { cases h with f, refine ⟨f $ sum.inl ⟨⟩, f $ sum.inr ⟨⟩, _⟩, intro h, cases f.2 h }

lemma exists_unequal_element (h : (2 : cardinal) ≤ mk α) (x : α) : ∃y : α, x ≠ y :=
begin
  rcases exists_two_elements h with ⟨y, z, h⟩,
  refine classical.by_cases (λ(h' : x = y), _) (λ h', ⟨y, h'⟩), rw [←h'] at h, exact ⟨z, h⟩
end

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

-- set_option pp.notation false
-- #print has_sep
-- example {s t : set α} : {x | x ∈ s ∧ x ∈ t} = { x ∈ s | x ∈ t} :=
-- begin
--  refl
-- end

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

lemma mk_image_eq_lift {α : Type u} {β : Type v} (f : α → β) (s : set α) (h : injective f) :
  lift.{v u} (mk (f '' s)) = lift.{u v} (mk s) :=
quotient.sound ⟨equiv.ulift.trans ((equiv.set.image f s h).symm.trans equiv.ulift.symm)⟩

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

lemma mk_sep (s : set α) (t : α → Prop) : mk ({ x ∈ s | t x } : set α)  = mk { x : s | t x.1 } :=
by { refine quotient.sound ⟨_⟩, symmetry, apply (subtype_subtype_equiv_subtype _ _).trans _,
     simp only [exists_prop, mem_sep_eq, set_coe_eq_subtype, mem_set_of_eq] }

-- lemma mk_set_subtype (s : set α) (t : α → Prop) :
--   mk { x : s // t x.1 } = mk ({ x ∈ s | t x } : set α) :=


lemma mk_sUnion_le {α : Type u} (A : set (set α)) :
  mk (⋃₀ A) ≤ mk A * cardinal.sup.{u u} (λ s : A, mk s) :=
by { rw [sUnion_eq_Union], refine le_trans mk_Union_le_sum_mk (sum_le_sup _) }

lemma mk_bUnion_le {ι α : Type u} (A : ι → set α) (s : set ι) :
  mk (⋃(x ∈ s), A x) ≤ mk s * cardinal.sup.{u u} (λ x : s, mk (A x.1)) :=
by { rw [bUnion_eq_Union], refine le_trans mk_Union_le_sum_mk (sum_le_sup _) }

lemma finset_card_lt_omega (s : finset α) : mk (↑s : set α) < omega :=
by { rw [lt_omega_iff_fintype], exact ⟨finset.subtype.fintype s⟩ }

-- lemma mk_set (α : Type u) : mk (set α) = 2 ^ mk α :=
-- sorry

lemma mk_preimage_of_injective_lift {α : Type u} {β : Type v} (f : α → β) (s : set β)
  (h : injective f) : lift.{u v} (mk (f ⁻¹' s)) ≤ lift.{v u} (mk s) :=
begin
  constructor, apply embedding.congr equiv.ulift.symm equiv.ulift.symm,
  use subtype.coind (λ x, f x.1) (λ x, x.2),
  apply subtype.coind_injective, exact injective_comp h subtype.val_injective
end

lemma mk_preimage_of_onto_lift {α : Type u} {β : Type v} (f : α → β) (s : set β)
  (h : s ⊆ range f) : lift.{v u} (mk s) ≤ lift.{u v} (mk (f ⁻¹' s)) :=
begin
  constructor, apply embedding.congr equiv.ulift.symm equiv.ulift.symm,
  fsplit,
  { rintro ⟨y, hy⟩, rcases classical.psigma_of_exists (h hy) with ⟨x, rfl⟩, exact ⟨x, hy⟩ },
  rintro ⟨y, hy⟩ ⟨y', hy'⟩, dsimp,
  rcases classical.psigma_of_exists (h hy) with ⟨x, rfl⟩,
  rcases classical.psigma_of_exists (h hy') with ⟨x', rfl⟩,
  simp, intro hxx', rw hxx'
end

lemma mk_preimage_of_injective_of_onto_lift {α : Type u} {β : Type v} (f : α → β) (s : set β)
  (h : injective f) (h2 : s ⊆ range f) : lift.{u v} (mk (f ⁻¹' s)) = lift.{v u} (mk s) :=
by { apply le_antisymm (mk_preimage_of_injective_lift f s h) (mk_preimage_of_onto_lift f s h2) }

lemma mk_preimage_of_injective (f : α → β) (s : set β) (h : injective f) :
  mk (f ⁻¹' s) ≤ mk s :=
by { convert mk_preimage_of_injective_lift.{u u} f s h using 1; rw [lift_id] }

lemma mk_preimage_of_onto (f : α → β) (s : set β) (h : s ⊆ range f) :
  mk s ≤ mk (f ⁻¹' s) :=
by { convert mk_preimage_of_onto_lift.{u u} f s h using 1; rw [lift_id] }

lemma mk_preimage_of_injective_of_onto (f : α → β) (s : set β)
  (h : injective f) (h2 : s ⊆ range f) : mk (f ⁻¹' s) = mk s :=
by { convert mk_preimage_of_injective_of_onto_lift.{u u} f s h h2 using 1; rw [lift_id] }

lemma mk_subset_ge_of_subset_image_lift {α : Type u} {β : Type v} (f : α → β) {s : set α}
  {t : set β} (h : t ⊆ f '' s) :
    lift.{v u} (mk t) ≤ lift.{u v} (mk ({ x ∈ s | f x ∈ t } : set α)) :=
by { rw [image_eq_range] at h, convert mk_preimage_of_onto_lift _ _ h using 1, rw [mk_sep], refl }

lemma mk_subset_ge_of_subset_image (f : α → β) {s : set α} {t : set β} (h : t ⊆ f '' s) :
  mk t ≤ mk ({ x ∈ s | f x ∈ t } : set α) :=
by { rw [image_eq_range] at h, convert mk_preimage_of_onto _ _ h using 1, rw [mk_sep], refl }

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

lemma countable_iff (s : set α) : countable s ↔ mk s ≤ omega :=
begin
  rw [countable_iff_exists_injective], split,
  rintro ⟨f, hf⟩, exact ⟨embedding.trans ⟨f, hf⟩ equiv.ulift.symm.to_embedding⟩,
  rintro ⟨f'⟩, cases embedding.trans f' equiv.ulift.to_embedding with f hf, exact ⟨f, hf⟩
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
  { intro f, use sum.inl ⁻¹' range f,
    refine le_trans (mk_preimage_of_injective _ _ (λ x y, sum.inl.inj)) _,
    apply mk_range_le },
  rintro ⟨s, ⟨g⟩⟩,
  use λ y, if h : ∃(x : s), g x = y then sum.inl (classical.some h).val else sum.inr ⟨⟩,
  apply subtype.eq, ext,
  split,
  { rintro ⟨y, h⟩, dsimp only at h, by_cases h' : ∃ (z : s), g z = y,
    { rw [dif_pos h'] at h, cases sum.inl.inj h, exact (classical.some h').2 },
    { rw [dif_neg h'] at h, cases h }},
  { intro h, have : ∃(z : s), g z = g ⟨x, h⟩, exact ⟨⟨x, h⟩, rfl⟩,
    use g ⟨x, h⟩, dsimp only, rw [dif_pos this], congr',
    suffices : classical.some this = ⟨x, h⟩, exact congr_arg subtype.val this,
    apply g.2, exact classical.some_spec this }
end

lemma mk_bounded_set_le (α : Type u) (c : cardinal) :
  mk {t : set α // mk t ≤ c} ≤ max (mk α) omega ^ c :=
begin
  transitivity mk {t : set (ulift.{u} nat ⊕ α) // mk t ≤ c},
  { refine ⟨embedding.subtype_map _ _⟩, apply embedding.image,
    use sum.inr, apply sum.inr.inj, intros s hs, exact le_trans (mk_image_le _ _) hs },
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

lemma mk_bounded_subset_le {α : Type u} (s : set α) (c : cardinal.{u}) :
  mk {t : set α // t ⊆ s ∧ mk t ≤ c} ≤ max (mk s) omega ^ c :=
begin
  refine le_trans _ (mk_bounded_set_le s c),
  refine ⟨embedding.cod_restrict _ _ _⟩,
  use λ t, subtype.val ⁻¹' t.1,
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
  use x, apply le_antisymm _ (le_of_not_gt h),
  rw [le_mk_iff_exists_set], exact ⟨_, rfl⟩
end

/-- pigeonhole principle for a cardinality below the cardinality of the domain -/
theorem infinite_pigeonhole_card {β α : Type u} (f : β → α) (θ : cardinal) (hθ : θ ≤ mk β)
  (h₁ : cardinal.omega ≤ θ) (h₂ : mk α < θ.ord.cof) : ∃a : α, θ ≤ mk (f ⁻¹' {a}) :=
begin
  rcases le_mk_iff_exists_set.1 hθ with ⟨s, rfl⟩,
  cases infinite_pigeonhole (f ∘ subtype.val : s → α) h₁ h₂ with a ha,
  use a, rw [←ha, @preimage_comp _ _ _ subtype.val f],
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

section delta_system
variables {ι : Type w} {ι' : Type w'} {α : Type u} {β : Type v} {A : ι → set α}
def is_delta_system (A : ι → set α) :=
∃(root : set α), ∀{{x y}}, x ≠ y → A x ∩ A y = root

open cardinal
def root_subset (hι : 2 ≤ mk ι) {root : set α} (x : ι)
  (h : ∀{{x y}}, x ≠ y → A x ∩ A y = root) : root ⊆ A x :=
begin
  cases exists_unequal_element hι x with y hy, rw [←h hy], apply inter_subset_left
end

def finite_root (hι : 2 ≤ mk ι) {root : set α} (h2A : ∀(x : ι), finite (A x))
  (h : ∀{{x y}}, x ≠ y → A x ∩ A y = root) : finite root :=
begin
  rcases exists_two_elements hι with ⟨t, u, htu⟩,
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
  intro i, simp [equiv.apply_inverse_apply, comp_app],
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
  haveI := decidable_linear_order_of_is_well_order θr,
  let nr : ι → ρ → θ := λ i ξ, (h2A i ξ).val,
  let good : ρ → Prop := λ ξ, unbounded θr (range $ λ i, nr i ξ),
  have : ∃ξ : ρ, good ξ,
  { apply unbounded_of_unbounded_Union θr (λ ξ, range $ λ i, nr i ξ),
    { rw [Union_range_eq_Union], exact h3A, intro i, exact (h2A i).to_equiv.bijective.2 },
    { rw [cof_type_eq, ←θtype_eq, hθ.2], refine lt_trans hρ hκθ }},
  let ξ₀ : ρ := ρwo.wf.min good (ne_empty_of_exists_mem this),
  let α₀ : ordinal := sup.{u u} (λ o : {x // ρr x ξ₀}, sup.{u u} $ λ x : ι,
    ordinal.succ $ typein θr $ nr x o.1),
  have hα₀ : α₀ < type θr ,
  { rw [←θtype_eq], apply sup_lt_ord_of_is_regular _ hθ,
    { refine lt_of_le_of_lt _ (lt_trans hρ hκθ), rw [typein_card_eq, ←card_type ρr],
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
    (λ μ pick, classical.some $ this $ nth θr $ ⟨pick' μ pick, pick'_lt μ pick⟩),
  have lt_pick : ∀(μ : θ),
    θr (nth θr $ ⟨pick' μ (λ y _, pick y), pick'_lt μ (λ y _, pick y)⟩) (nr (pick μ) ξ₀),
  { intro μ, dsimp [pick], rw [θwo.wf.fix_eq _ μ], apply classical.some_spec (this _) },
  have pick_lt_pick : ∀{μ ν : θ} (h : θr ν μ) (η : ρ),
    θr (nr (pick ν) η) (nr (pick μ) ξ₀),
  { intros, apply trans_trichotomous_left _ (lt_pick μ), rw [←typein_le_typein, typein_nth],
    refine le_trans _ (le_max_right _ _), refine le_trans _ (le_sup _ ⟨η, ν, h⟩), refl },
  let sub_α₀ : set θ := typein θr ⁻¹' {c | c < α₀},
  have h1sub_α₀ : mk ↥sub_α₀ = α₀.card,
  { rw [←cardinal.lift_inj.{_ u+1}, mk_preimage_of_injective_of_onto_lift],
    rw [mk_initial_seg, cardinal.lift_lift],
    exact injective_typein θr,
    intros o ho,
    rcases typein_surj θr (lt_trans ho hα₀) with ⟨_, rfl⟩,
    apply mem_range_self },
  have h2A2' : ∀{x y : θ}, θr x y → A (pick x) ∩ A (pick y) ⊆ sub_α₀,
  { rintros x y hxy z ⟨hzx, hzy⟩,
    let η := typein (subrel θr $ A $ pick y) ⟨z, hzy⟩,
    have η_def : z = (nth (subrel θr $ A $ pick y) ⟨η, typein_lt_type _ _⟩).val, {rw [nth_typein]},
    cases lt_or_ge η (typein ρr ξ₀) with h h,
    { rw [mem_preimage_eq, mem_set_of_eq],
      refine lt_of_lt_of_le _ (ordinal.le_sup _ _),
      { refine ⟨nth ρr ⟨η, lt_trans h (typein_lt_type _ _)⟩, _⟩,
        rw [←typein_lt_typein ρr, typein_nth], exact h },
      refine lt_of_lt_of_le _ (ordinal.le_sup _ (pick y)),
      convert lt_succ_self (typein θr z), rw [η_def],
      dsimp [nr], congr' 1, apply order_iso_nth' (h2A _) },
    exfalso,
    have η_lt : η < type ρr,
    { convert typein_lt_type (subrel θr $ A $ pick y) ⟨z, hzy⟩ using 1, apply quotient.sound,
      exact ⟨h2A (pick y)⟩ },
    have : ¬ρr (nth ρr ⟨η, η_lt⟩) ξ₀, { rw [←typein_le_typein, typein_nth], exact h },
    apply this,
    rw [(h2A (pick y)).ord], dsimp only [subrel, order.preimage],
    convert pick_lt_pick hxy ((h2A (pick x)).symm ⟨z, hzx⟩) using 1,
    transitivity z, { rw [η_def], congr' 1, apply order_iso_nth (h2A _) },
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
  let codomain := {s : set θ // s ⊆ sub_α₀ ∧ mk s ≤ mk ρ},
  have hsub_α₀ : mk ↥sub_α₀ < mk θ,
  { rw [h1sub_α₀, ←ord_lt_ord, θtype_eq], refine lt_of_le_of_lt (ord_card_le _) hα₀ },
  have hcodomain : ∀(x : range pick), A x ∩ sub_α₀ ⊆ sub_α₀ ∧ mk (↥(A x ∩ sub_α₀)) ≤ mk ρ,
  { have α₀_lt_pick : ∀(μ : θ), θr (nth θr ⟨α₀, hα₀⟩) (nr (pick μ) ξ₀),
    { intro μ, apply trans_trichotomous_left _ (lt_pick μ), rw nth_le_nth, apply le_max_left },
    rintro ⟨s, hs⟩, refine ⟨inter_subset_right _ _, _⟩,
    rcases hs with ⟨μ, rfl⟩, dsimp,
    transitivity mk {x : A (pick μ) // typein θr x.1 < α₀},
    { apply le_of_eq, apply mk_sep },
    let f := (h2A (pick μ)).to_equiv,
    rw [mk_subtype_of_equiv _ f.symm],
    transitivity mk { x : ρ // ρr x ξ₀},
    { apply mk_le_of_subproperty, intros x hx,
      rw [(h2A (pick μ)).ord], dsimp only [subrel, order.preimage],
      refine trans _ (α₀_lt_pick μ),
      rw [←nth_typein θr (f x).val, ←nth_lt_nth θr], exact hx },
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
    { rw [mk_image_eq _ _ subtype.val_injective, ←h1A2, ←hr'] },
    { rintro _ ⟨⟨x, hx⟩, hx', rfl⟩,
      simpa only [set.mem_singleton_iff, set.mem_preimage_eq, f, subtype.ext] using hx' }},
  rcases this with ⟨r, t, hr, h1t, h2t, h3t⟩,
  refine ⟨t, h2t, r, _⟩,
  intros x y hxy, rw [←h3t x.2], apply set.ext, intro z, split,
  intro hz, refine ⟨hz.1, h2A2 ⟨x, h1t x.2⟩ ⟨y, h1t y.2⟩ _ hz⟩,
  intro h, apply hxy, apply subtype.eq, apply congr_arg subtype.val h,
  intro hz, refine ⟨hz.1, _⟩, rw [h3t x.2, ←h3t y.2] at hz, exact hz.1
end

local attribute [instance] [priority 0] classical.prop_decidable
lemma delta_system_lemma_1 {κ : cardinal} (hκ : cardinal.omega ≤ κ)
  {θ : Type u} (θr : θ → θ → Prop) [θwo : is_well_order θ θr] (hκθ : κ < mk θ)
  (hθ : is_regular $ mk θ) (θtype_eq : ord (mk θ) = type θr) (hθ_le : ∀(β < mk θ), β ^< κ < mk θ)
  {ρ : Type u} (ρr : ρ → ρ → Prop) [ρwo : is_well_order ρ ρr] (hρ : mk ρ < κ)
  {ι : Type u} {A : ι → set θ} (h2A : ∀i, ρr ≃o subrel θr (A i)) (hι : mk θ = mk ι) :
    ∃(t : set ι), mk t = mk θ ∧ is_delta_system (restrict A t) :=
begin
  by_cases h3A : unbounded θr (⋃i, A i),
  exact delta_system_lemma_2 hκ θr hκθ hθ θtype_eq hθ_le ρr hρ h2A h3A,
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
  rw [ord_le, typein, card_type], apply mk_le_of_subset hμ
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
    rw [mk_image_eq], rw [mk_preimage_of_injective_of_onto], apply h2A i,
    apply subtype.val_injective, apply h2β (mem_image_of_mem _ hi), exact f.2 },
  have hκθ' : mk κα < cof (ord (mk θ)),
  { rw [←card_type κr, type_out, card_ord], convert hκθ, exact hθ.2 },
  let g : t₁ → κα := λ i : t₁, nth κr ⟨type (subrel θr (A₀ i)), h3A₀ i⟩,
  rcases infinite_pigeonhole_set g (mk θ) (ge_of_eq ht₁) hθ.1 hκθ' with ⟨ρ', t₂, ht₂, h2t₂, h3t₂⟩,
  let ρ := { x : κα | x < ρ' },
  let ρr := subrel κr ρ,
  have hρ : mk ρ < κ, { exact card_typein_out_lt κ ρ', },
  have h4A₁ : Π(i : t₂), ρr ≃o subrel θr (A₀ i),
  { rintro ⟨i, hi⟩, symmetry,
    have : type (subrel θr (A₀ i)) = typein κr ρ', { rw [← h3t₂ hi, typein_nth], refl },
    exact classical.choice (quotient.exact this) },
  have h4t₂ : mk θ = mk ↥t₂,
  { apply le_antisymm h2t₂, convert mk_le_of_subset ht₂ using 1, rw ht₁, refl },
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
  { rw [restrict_def, is_delta_system_image] at h2t, swap, exact equiv.ulift.symm.bijective.1,
    rw [is_delta_system_precompose_iff (equiv.set.image _ _ _)],
    swap, exact equiv.ulift.bijective.1,
    convert h2t, apply funext, rintro ⟨x, hx⟩, refl },
  { rw [←cardinal.lift_lt, cardinal.lift_omega, ←cardinal.succ_le] at h, exact h },
  rintro ⟨i⟩, rw [lt_omega_iff_finite], apply finite_image, exact h2A i
end

end delta_system

namespace set

variables {α β : Type u}
open cardinal

lemma finite_of_finite_image_of_inj_on (f : α → β) (s : set α) (hf : inj_on f s)
  (h : finite (f '' s)) : finite s :=
by { rw [←lt_omega_iff_finite] at h ⊢, rwa [mk_image_eq_of_inj_on f s hf] at h }

lemma countable_of_embedding {s : set α} {t : set β} (f : s ↪ t) (h : countable t) : countable s :=
begin
  rw [countable_iff], rw [countable_iff] at h,
  refine le_trans _ h, refine ⟨f⟩
end

def pairwise_disjoint (s : set (set α)) : Prop :=
∀{{x y : set α}}, x ∈ s → y ∈ s → x ≠ y → x ∩ y = ∅

lemma pairwise_disjoint_subset {s t : set (set α)} (h : s ⊆ t)
  (ht : pairwise_disjoint t) : pairwise_disjoint s :=
by { rintro x y hx hy hxy, exact ht (h hx) (h hy) hxy }

lemma disjoint_of_subset {s t s' t' : set α} (hst : s ∩ t = ∅) (hs : s' ⊆ s) (ht : t' ⊆ t) :
  s' ∩ t' = ∅ :=
by { apply subset.antisymm, convert inter_subset_inter hs ht, rw hst, apply empty_subset }

lemma pairwise_disjoint_range {s : set (set α)} (f : s → set α) (hf : ∀(x : s), f x ⊆ x.1)
  (ht : pairwise_disjoint s) : pairwise_disjoint (range f) :=
begin
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩ hxy, refine disjoint_of_subset (ht x.2 y.2 _) (hf x) (hf y),
  intro h, apply hxy, apply congr_arg f, exact subtype.eq h
end

local attribute [instance] [priority 0] classical.prop_decidable
lemma pairwise_disjoint_elim {s : set (set α)} (h : pairwise_disjoint s) {x y : set α}
  (hx : x ∈ s) (hy : y ∈ s) (z : α) (hzx : z ∈ x) (hzy : z ∈ y) : x = y :=
begin
  by_contra,
  have : x ∩ y ≠ ∅, { rw [ne_empty_iff_exists_mem], exact ⟨z, ⟨hzx, hzy⟩⟩ },
  exact this (h hx hy a)
end

lemma exists_finset_of_finite {s : set α} (h : finite s) : ∃(s' : finset α), s'.to_set = s :=
by { have := h, cases this, exactI ⟨to_finset s, set.ext $ λ x, mem_to_finset⟩ }

def eq_on' {α} {β : α → Type*} (f g : ∀x, β x) (s : set α) : Prop :=
∀{{x}}, x ∈ s → f x = g x

lemma eq_on'_iff {α} {β : α → Type*} (f g : ∀x, β x) (s : set α) :
  eq_on' f g s ↔ restrict f s = restrict g s :=
begin
  split, intros h, apply funext, rintro ⟨x, hx⟩, exact h hx,
  intros h x hx, apply congr_fun h ⟨x, hx⟩
end

lemma mem_diff_singleton_empty {s : set α} {t : set (set α)} :
  s ∈ t \ {∅} ↔ (s ∈ t ∧ nonempty s) :=
by simp [ne_empty_iff_exists_mem.symm]

lemma nmem_singleton_empty {s : set α} : s ∉ ({∅} : set (set α)) ↔ nonempty s :=
by simp [ne_empty_iff_exists_mem.symm]

lemma nonempty_compl {s : set α} : s ≠ univ ↔ nonempty (-s : set α) :=
by { rw [coe_nonempty_iff_ne_empty, not_iff_not],
     split, intro h, rw [h, compl_univ],
     intro h, rw [←compl_compl s, h, compl_empty] }

end set

lemma finite.coe_to_finset {α} {s : set α} (h : finite s) : ↑h.to_finset = s :=
by { ext, apply mem_to_finset }

-- namespace topological_space

open set topological_space cardinal

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
  have f : ∀(x : s), Σ'(y : set α), y ∈ B ∧ y ≠ ∅ ∧ y ⊆ x.1,
  { rintro ⟨x, hx⟩, apply classical.psigma_of_exists,
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
    rcases classical.psigma_of_exists this with ⟨x, ⟨hx, h2x⟩⟩,
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

section topological_space
open lattice filter
variables {α : Type u} {β : Type v} {ι : Type w} {π : ι → Type w'} [∀x, topological_space (π x)]

variables [t : topological_space α] [topological_space β]

include t

lemma mem_opens {x : α} {o : opens α} : x ∈ o ↔ x ∈ o.1 := by refl

lemma is_open_map_of_is_topological_basis {s : set (set α)}
  (hs : is_topological_basis s) (f : α → β) (hf : ∀x ∈ s, is_open (f '' x)) :
  is_open_map f :=
begin
  intros o ho,
  rcases Union_basis_of_is_open hs ho with ⟨γ, g, rfl, hg⟩,
  rw [image_Union], apply is_open_Union, intro i, apply hf, apply hg
end

lemma subbasis_subset_basis {s : set (set α)} (hs : t = generate_from s) :
  s \ {∅} ⊆ ((λf, ⋂₀ f) '' {f:set (set α) | finite f ∧ f ⊆ s ∧ ⋂₀ f ≠ ∅}) :=
begin
  intros o ho, refine ⟨{o}, ⟨finite_singleton o, _, _⟩, _⟩,
  { rw [singleton_subset_iff], exact ho.1 },
  { rw [sInter_singleton], refine mt mem_singleton_iff.mpr ho.2 },
  dsimp only, rw [sInter_singleton]
end

end topological_space

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
  { rw [generate_from_le_iff_subset_is_open], rintro _ ⟨⟨i, o, ho⟩, rfl⟩,
    apply generate_open.basic, apply mem_bUnion (mem_range_self i), exact ⟨o, ho, rfl⟩ },
  refine lattice.supr_le _, intro i,
  rintro _ ⟨s, hs, rfl⟩, apply generate_open.basic, exact ⟨⟨i, s, hs⟩, rfl⟩
end

def pi_basis : set (set (Πx, β x)) :=
(λf, ⋂₀ f) '' {f : set (set (Πx, β x)) | finite f ∧ f ⊆ pi_subbasis β ∧ ⋂₀ f ≠ ∅ }

-- local attribute [instance] [priority 0] classical.prop_decidable
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
  rw [pi_subbasis, subset_range_iff] at h2o, rcases h2o with ⟨o', rfl⟩,
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
      have h₂ : nonempty (-o.1 : set (β x)), { rw [←nonempty_compl], exact hx.2 },
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
      { apply finite_image, apply finite_preimage _ h2o', intros o o' hoo',
        cases hoo', refl },
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

local attribute [instance] [priority 0] classical.prop_decidable
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
  apply funext, rintro ⟨i, hi⟩, dsimp only, rw [restrict, dif_pos hi]
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
  { apply finite.to_finset (finite_preimage subtype.val_injective t.finite_to_set) },
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
    have h₂ : nonempty (-(s x) : set _), { rw [←nonempty_compl], exact hs },
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
  { apply subbasis_subset_basis (is_subbasis_pi β), split,
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
  have h2'D : ∀(s t : set (Πx, β x)), s ∈ C'' → t ∈ C'' → s ≠ t → π '' s ∩ π '' t = ∅,
  { rintro s t hs ht hst,
    rw [eq_empty_iff_forall_not_mem],
    rintro f ⟨hfs, hft⟩,
    have := h2C (hC'' hs) (hC'' ht) (λ h, hst $ by rw h), rw [eq_empty_iff_forall_not_mem] at this,
    rcases hfs with ⟨g₁, hg₁, rfl⟩,
    rcases hft with ⟨g₂, hg₂, hg⟩,
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
  { rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩ hst, apply h2'D s t hs ht, intro h, apply hst, rw h },
  have h3D : cardinal.omega < mk D,
  { rw [mk_image_eq_of_inj_on, mk_image_eq], exact h1C',
    apply subtype.val_injective,
    intros s t hs ht hst, by_contradiction hst',
    apply ne_of_disjoint _ (h2'D s t hs ht hst') hst,
    apply nonempty_image, apply nonempty_of_mem_pi_basis (hC $ hC'' hs) },
  apply not_le_of_gt h3D, rw [←countable_iff], exact h R h2R D hD h2D
end

end pi
