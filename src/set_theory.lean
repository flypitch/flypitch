import .to_mathlib

universe variables u v w
noncomputable theory

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

lemma mk_univ (α : Type u) : mk (@set.univ α) = mk α :=
quotient.sound ⟨equiv.set.univ α⟩

lemma mk_image_le {α β : Type u} (f : α → β) (s : set α) : mk (f '' s) ≤ mk s :=
begin
  constructor, fapply function.embedding.of_surjective,
  { rintro ⟨x, hx⟩, exact ⟨f x, mem_image_of_mem f hx⟩ },
  { rintro ⟨y, ⟨x, hx, h⟩⟩, exact ⟨⟨x, hx⟩, subtype.eq h⟩ }
end

lemma mk_image_eq {α β : Type u} (f : α → β) (s : set α) (h : function.injective f) :
  mk (f '' s) = mk s :=
quotient.sound ⟨(equiv.set.image f s h).symm⟩

lemma mk_range_le {α β : Type u} (f : α → β) : mk (range f) ≤ mk α :=
begin
  constructor, fapply function.embedding.of_surjective,
  { intro x, exact ⟨f x, mem_range_self x⟩ },
  { intro y, rcases y.2 with ⟨x, h⟩, exact ⟨x, subtype.eq h⟩ }
end

lemma mk_range_eq {α β : Type u} (f : α → β) (h : function.injective f) : mk (range f) = mk α :=
quotient.sound ⟨(equiv.set.range f h).symm⟩

end cardinal

namespace function
lemma injective_of_increasing {α β} (r : α → α → Prop) (s : β → β → Prop) [is_trichotomous α r]
  [is_irrefl β s] (f : α → β) (hf : ∀{x y}, r x y → s (f x) (f y)) : injective f :=
begin
  intros x y hxy,
  rcases trichotomous_of r x y with h | h | h,
  have := hf h, rw hxy at this, exfalso, exact irrefl_of s (f y) this,
  exact h,
  have := hf h, rw hxy at this, exfalso, exact irrefl_of s (f y) this
end

end function

namespace ordinal

variables {α : Type u} {β : Type v} {γ : Type w}
local attribute [instance] [priority 0] classical.prop_decidable

def typesub (r : α → α → Prop) [is_well_order α r] (s : set α) : ordinal :=
type (subrel r s)

/-- The function α^{<β}, defined to be sup_{γ < β} α^γ -/
def powerlt (α β : ordinal.{u}) : ordinal.{u} :=
bsup.{u u} β (λ γ _, power α γ)

-- def strict_upper_bounds [has_lt α] (s : set α) : set α := { x | ∀a ∈ s, a < x }
-- def unbounded {α : Type u} [preorder α] (s : set α) : Prop := strict_upper_bounds s = ∅

@[simp] lemma not_bounded_iff {r : α → α → Prop} (s : set α) : ¬bounded r s ↔ unbounded r s :=
by simp only [bounded, unbounded, not_forall, not_exists, exists_prop, not_and, not_not]

@[simp] lemma not_unbounded_iff {r : α → α → Prop} (s : set α) : ¬unbounded r s ↔ bounded r s :=
by simp only [bounded, unbounded, not_forall, not_exists, exists_prop, not_and, not_not]

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

def typein' (r : α → α → Prop) [is_well_order α r] : r ≃o subrel (<) (< type r) :=
⟨⟨λ x, ⟨typein r x, typein_lt_type r x⟩, nth r, nth_typein r, λ y, subtype.eq (typein_nth r y)⟩,
  λ a b, (typein_lt_typein r).symm⟩

lemma nth_lt_nth (r : α → α → Prop) [is_well_order α r] {o o' : {x // x < type r}} :
  o.1 < o'.1 ↔ r (nth r o) (nth r o') :=
begin
  rw [(typein' r).ord], dsimp [subrel, typein'], rw [typein_nth, typein_nth], refl
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

-- lemma lt_ord_succ_card (o : ordinal) : o < o.card.succ.ord :=
-- sorry

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
theorem infinite_pigeonhole {α β : Type u} (f : β → α) (h₁ : cardinal.omega ≤ mk β)
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



end ordinal
open ordinal

def is_delta_system {α : Type u} (A : set (set α)) :=
∃(root : set α), ∀(x y ∈ A), x ≠ y → x ∩ y = root

namespace subrel

-- instance subrel.is_well_order' {α : Type u} (r : α → α → Prop) [is_well_order α r]
--   (p : α → Prop) : is_well_order {x // p x} (subrel r p) :=
-- subrel.is_well_order r p

end subrel

namespace delta_system

open cardinal ordinal set
-- lemma delta_system_lemma_4 (κ : cardinal) (hκ : cardinal.omega ≤ κ)
--   {θ : Type u} (θr : θ → θ → Prop) [θwo : is_well_order θ θr] (hκθ : κ < mk θ)
--   (hθ : is_regular $ mk θ) (θtype_eq : type θr = ord (mk θ))
--   --(hθ_le : ∀(β < type θr), card (powerlt β κ.ord) < mk θ)
--   {ρ : ordinal} (hρ : ρ < κ.ord)
--   {A : set (set θ)} (hA : mk (subtype A) = mk θ) (hA2 : ∀{s : set θ} (h : s ∈ A),
--     type (subrel θr s) = ρ)
--   (hA3 : unbounded θr (⋃₀ A)) :
--   ∃(B ⊆ A), mk B = mk θ ∧ is_delta_system B :=
-- begin
--   let ι : θ → ordinal := typein θr,
--   let nr : A → {o // o < ρ} → θ :=
--     λ s ξ, (nth (subrel θr s.val) ⟨ξ, by rw [hA2 s.2]; exact ξ.2⟩).val,
--   let good : {o // o < ρ} → Prop := λ ξ, unbounded θr (range $ λ x, nr x ξ),
--   have : ∃ξ : {o // o < ρ}, good ξ,
--   { apply unbounded_indexed_partition (λ ξ, range $ λ x, nr x ξ),
--     { rw [Union_range_eq_sUnion], exact hA3, intro s, exact (hA2 s.2).to_equiv.symm.bijective.2 },
--     { rw [cof_type_eq, θtype_eq, hθ.2], refine lt_trans hρ hκθ }},
--   let ξ₀ : ρ := ρwo.wf.min good (ne_empty_of_exists_mem this),
--   -- have : ∀(x : θ), ∃y, θr x y,
--   -- { intro y, apply has_succ_of_is_limit, rw [θtype_eq], exact ord_is_limit hθ.1 },
--   -- have : bounded θr ((λ x : A × ρ, θwo.wf.succ (nr x.1 x.2) (this _)) ''
--   --   set.prod set.univ {x | ρr x ξ₀}),
--   -- { sorry },
--   -- let α₀ : ordinal := ι (θwo.wf.sup _ this),
--   -- let α₀ : ordinal := sup.{u u} (λ x : A × {x // ρr x ξ₀}, ordinal.succ $ ι $ nr x.1 x.2.1),
--   let α₀ : ordinal := sup.{u u} (λ o : {x // ρr x ξ₀}, sup.{u u} $ λ s : A,
--     ordinal.succ $ ι $ nr s o.1),
--   -- let α₀ : ordinal := bsup.{u u} (typein ρr ξ₀) (λ o ho, sup.{u u} $ λ s : A,
--   --   ordinal.succ $ ι $ nr s _),
--   have : α₀ < type θr, { rw [θtype_eq], apply sup_lt_ord_of_is_regular _ hθ,
--     refine lt_of_le_of_lt _ (lt_trans hρ hκθ), sorry,
--     rintro ⟨ξ, hξ⟩, apply lt_of_not_ge, intro h,
--     apply ρwo.wf.not_lt_min _ _ _ hξ, sorry },
--   have : ∀(x : θ), ∃s : A, θr x (nr s ξ₀),
--   { intro x, have : good ξ₀ := ρwo.wf.min_mem good _,
--      rcases this x with ⟨y, ⟨s, rfl⟩, hy⟩,
--     refine ⟨s, _⟩, sorry },
--   let pick : θ → A := θwo.wf.fix
--   /- need to take the successor of x here -/
--     (λ μ ih, classical.some $ this $ nth θr $ ⟨(ordinal.sup.{u u} (λ x : ρ × subtype {x | θr x μ}, max α₀ $ ι $ nr (ih x.2.val x.2.2) x.1)), sorry⟩),
--   let A2 := range (subtype.val ∘ pick),
--   have h1A2 : mk A2 = mk θ, sorry,
--   let sub_α₀ : set θ := ι ⁻¹' {c | c ≤ α₀ },
--   have h2A2 : ∀(x ∈ A2) (y ∈ A2), x ≠ y → x ∩ y ⊆ sub_α₀, sorry,
--   have : ∃r B, r ⊆ sub_α₀ ∧ B ⊆ A2 ∧ mk B = mk θ ∧ ∀(x ∈ B), x ∩ sub_α₀ = r, sorry,
--   { rcases this with ⟨r, B, hr, h1B, h2B, h3B⟩,
--     refine ⟨B, subset.trans h1B _, h2B, r, _⟩, rw [range_subset_iff], intro x, exact (pick x).2,
--     intros x y hx hy hxy, rw [←h3B x hx], apply set.ext, intro z, split,
--     intro hz, refine ⟨hz.1, h2A2 x (h1B hx) y (h1B hy) hxy hz⟩,
--     intro hz, refine ⟨hz.1, _⟩, rw [h3B x hx, ←h3B y hy] at hz, exact hz.1 },
-- end


/- start with ρ as an ordinal

lemma delta_system_lemma_3 (κ : cardinal) (hκ : cardinal.omega ≤ κ)
  {θ : Type u} (θr : θ → θ → Prop) [θwo : is_well_order θ θr] (hκθ : κ < mk θ)
  (hθ : is_regular $ mk θ) (θtype_eq : type θr = ord (mk θ))
  --(hθ_le : ∀(β < type θr), card (powerlt β κ.ord) < mk θ)
  {ρ : ordinal} (hρ : ρ < κ.ord)
  {A : set (set θ)} (hA : mk (subtype A) = mk θ)
  (hA2 : ∀{s : set θ} (h : s ∈ A), type (subrel θr s) = ρ)
  (hA3 : unbounded θr (⋃₀ A)) :
  ∃(B ⊆ A), mk B = mk θ ∧ is_delta_system B :=
begin
  haveI := decidable_linear_order_of_is_well_order θr,
  let ι : θ → ordinal := typein θr,
  let nr : A → {x // x < ρ} → θ :=
  λ s ξ, (nth (subrel θr s.val) ⟨ξ.val, by { rw [hA2 s.2], exact ξ.2 }⟩).val,
  let good : {x // x < ρ} → Prop := λ ξ, unbounded θr (range $ λ x, nr x ξ),
  have : ∃ξ : {x // x < ρ}, good ξ,
  { apply unbounded_indexed_partition (λ ξ, range $ λ x, nr x ξ),

-/

lemma sup_succ {ι} (f : ι → ordinal) : sup (λ i, succ (f i)) ≤ succ (sup f) :=
by { rw [ordinal.sup_le], intro i, rw ordinal.succ_le_succ, apply ordinal.le_sup }

open function
lemma delta_system_lemma_3 (κ : cardinal) (hκ : cardinal.omega ≤ κ)
  {θ : Type u} (θr : θ → θ → Prop) [θwo : is_well_order θ θr] (hκθ : κ < mk θ)
  (hθ : is_regular $ mk θ) (θtype_eq : type θr = ord (mk θ))
  (hθ_le : ∀(β < type θr), card (powerlt β κ.ord) < mk θ)
  {ρ : Type u} (ρr : ρ → ρ → Prop) [ρwo : is_well_order ρ ρr] (hρ : mk ρ < κ)
  {A : set (set θ)} (hA : mk (subtype A) = mk θ) (hA2 : ∀{s : set θ} (h : s ∈ A), ρr ≃o subrel θr s)
  (hA3 : unbounded θr (⋃₀ A)) :
  ∃(B ⊆ A), mk B = mk θ ∧ is_delta_system B :=
begin
  haveI := decidable_linear_order_of_is_well_order θr,
  let ι : θ → ordinal := typein θr,
  let nr : A → ρ → θ := λ s ξ, (hA2 s.2 ξ).val,
  let good : ρ → Prop := λ ξ, unbounded θr (range $ λ x, nr x ξ),
  have : ∃ξ : ρ, good ξ,
  { apply unbounded_of_unbounded_Union θr (λ ξ, range $ λ x, nr x ξ),
    { rw [Union_range_eq_sUnion], exact hA3, intro s, exact (hA2 s.2).to_equiv.bijective.2 },
    { rw [cof_type_eq, θtype_eq, hθ.2], refine lt_trans hρ hκθ }},
  let ξ₀ : ρ := ρwo.wf.min good (ne_empty_of_exists_mem this),
  let α₀ : ordinal := sup.{u u} (λ o : {x // ρr x ξ₀}, sup.{u u} $ λ s : A,
    ordinal.succ $ ι $ nr s o.1),
  have hα₀ : α₀ < type θr ,
  { rw [θtype_eq], apply sup_lt_ord_of_is_regular _ hθ,
    { refine lt_of_le_of_lt _ (lt_trans hρ hκθ), rw [typein_card_eq, ←card_type ρr],
    apply card_le_card, apply le_of_lt, apply typein_lt_type },
    rintro ⟨ξ, hξ⟩, refine lt_of_le_of_lt (sup_succ _) _,
    apply (ord_is_limit hθ.1).2, apply lt_of_not_ge, intro h,
    apply ρwo.wf.not_lt_min _ _ _ hξ, apply unbounded_range_of_sup_ge,
    dsimp, rw [θtype_eq], exact h },
  have θr_unbounded : ∀(x : θ), ∃y, θr x y,
  { intro y, apply has_succ_of_is_limit, rw [θtype_eq], exact ord_is_limit hθ.1 },
  have : ∀(x : θ), ∃s : A, θr x (nr s ξ₀),
  { intro x, have : good ξ₀ := ρwo.wf.min_mem good _,
    cases θr_unbounded x with y hy,
    rcases this y with ⟨z, ⟨s, rfl⟩, hz⟩,
    refine ⟨s, _⟩, rcases trichotomous_of θr (nr s ξ₀) y with hw | rfl | hw,
    exfalso, exact hz hw, exact hy, exact trans hy hw },
  let pick' : ∀(μ : θ), ∀(pick : ∀y, θr y μ → A), ordinal :=
  λ μ pick, max α₀ $ sup.{u u} (λ x : ρ × {x // θr x μ}, ι $ nr (pick x.2.val x.2.2) x.1),
  have pick'_lt : ∀(μ : θ) (pick : ∀y, θr y μ → A), pick' μ pick < type θr,
  { intros μ pick,
    apply max_lt hα₀,
    rw [θtype_eq],
    apply sup_lt_ord_of_is_regular _ hθ,
    { apply @mul_lt_of_lt (mk ρ) (mk {x // θr x μ}) _ hθ.1 (lt_trans hρ hκθ),
      rw [←ord_lt_ord, ←θtype_eq], apply lt_of_le_of_lt (ord_le_type (subrel θr {x | θr x μ})),
      apply typein_lt_type },
    rintro ⟨x, y, hy⟩, rw [←θtype_eq], apply typein_lt_type },
  let pick : θ → A := θwo.wf.fix
    (λ μ pick, classical.some $ this $ nth θr $ ⟨pick' μ pick, pick'_lt μ pick⟩),
  let A2 := range (subtype.val ∘ pick),
  have lt_pick : ∀(μ : θ),
    θr (nth θr $ ⟨pick' μ (λ y _, pick y), pick'_lt μ (λ y _, pick y)⟩) (nr (pick μ) ξ₀),
  { intro μ, dsimp [pick], rw [θwo.wf.fix_eq _ μ], apply classical.some_spec (this _) },
  have α₀_lt_pick : ∀(μ : θ), θr (nth θr ⟨α₀, hα₀⟩) (nr (pick μ) ξ₀),
  { intro μ, apply trans_trichotomous_left _ (lt_pick μ), rw nth_le_nth, apply le_max_left },
  have pick_lt_pick : ∀{μ ν : θ} (h : θr ν μ) (η : ρ),
    θr (nr (pick ν) η) (nr (pick μ) ξ₀),
  { intros, apply trans_trichotomous_left _ (lt_pick μ), rw [←typein_le_typein, typein_nth],
    refine le_trans _ (le_max_right _ _), refine le_trans _ (le_sup _ ⟨η, ν, h⟩), refl },
  have h1A2 : mk A2 = mk θ,
  { have increasing_pick : ∀{{x y : θ}}, θr x y → θr (nr (pick x) ξ₀) (nr (pick y) ξ₀),
    { intros x y hxy, apply pick_lt_pick hxy ξ₀ },
    have injective_pick : injective pick,
    { intros x y hx, apply injective_of_increasing _ _ _ increasing_pick, dsimp only,
      congr' 1, exact hx },
    rw [mk_range_eq], apply injective_comp, exact subtype.val_injective, apply injective_pick },
  let sub_α₀ : set θ := ι ⁻¹' {c | c < α₀},
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
  have : ∃r B, r ⊆ sub_α₀ ∧ B ⊆ A2 ∧ mk B = mk θ ∧ ∀(x ∈ B), x ∩ sub_α₀ = r,
  { have h1 : cardinal.omega ≤ mk ↥A2, { rw [h1A2], exact hθ.1 },
    have h2 : mk (set ↥sub_α₀) < cof (ord (mk ↥A2)), { sorry },
    cases infinite_pigeonhole (λ(s : A2), (subtype.val ⁻¹' s.val : set sub_α₀)) h1 h2 with r' hr',
    let r := subtype.val '' r',
    refine ⟨r, subtype.val '' ((λ (s : A2), s.val ∩ sub_α₀) ⁻¹' {r}), _, _, _, _⟩,
    { rintro _ ⟨⟨x, hx⟩, _, rfl⟩, exact hx },
    { rintro _ ⟨⟨x, hx⟩, _, rfl⟩, exact hx },
    { rw [mk_image_eq, ←h1A2, ←hr'], sorry, apply subtype.val_injective },
    { rintro _ ⟨⟨x, hx⟩, hx', rfl⟩,
      simpa only [set.mem_singleton_iff, set.mem_preimage_eq] using hx' }},
  rcases this with ⟨r, B, hr, h1B, h2B, h3B⟩,
  refine ⟨B, subset.trans h1B _, h2B, r, _⟩, rw [range_subset_iff], intro x, exact (pick x).2,
  intros x y hx hy hxy, rw [←h3B x hx], apply set.ext, intro z, split,
  intro hz, refine ⟨hz.1, h2A2 x (h1B hx) y (h1B hy) hxy hz⟩,
  intro hz, refine ⟨hz.1, _⟩, rw [h3B x hx, ←h3B y hy] at hz, exact hz.1
end
#exit
lemma delta_system_lemma_2 (κ : cardinal) (hκ : cardinal.omega ≤ κ) {θ : cardinal.{u}} (hκθ : κ < θ)
  (hθ : is_regular θ) (hθ_le : ∀(α < θ.ord), card (powerlt α κ.ord) < θ)
  (A : set (set ({μ // μ < θ}))) {ρ} (hρ : ρ < κ.ord)
  (hA: mk (subtype A) = θ) (hA2 : ∀{x : set θ.ord.out.α} (h : x ∈ A), typesub θ.ord.out.r x = ρ) :
  ∃(B ⊆ A), mk B = θ ∧ is_delta_system B :=
begin
  let ι : θ.ord.out.α → ordinal := typein θ.ord.out.r,
  let nr' : ∀(a : A), subtype (< ρ) → subtype a.val :=
    λ a ξ, (order_iso_out _).to_fun _,
  let nr : A → subtype (< ρ) → θ.ord.out.α :=
    λ a ξ, (order_iso_out _).to_fun _,
  let good : ρ.out.α → Prop := λ ξ, unbounded (range $ λ x, nr x ξ),
  have : ∃ξ : ρ.out.α, good ξ,
  { sorry },
  let ξ₀ : ρ.out.α := ρ.out.wo.wf.min { ξ | good ξ } (ne_empty_of_exists_mem this),
  have : ¬unbounded ((λ x : A × ρ.out.α, nr x.1 x.2) '' set.prod set.univ (< ξ₀)), sorry,
  let α₀ : ordinal := ι (θ.ord.out.wo.wf.strict_sup _ this),
  have : unbounded (⋃₀ A),
  { sorry },
  have : ∀(x < θ.ord), ∃y : A, x < ι (nr y ξ₀), sorry,
  let pick : θ.ord.out.α → A := θ.ord.out.wo.wf.fix
    (λ μ ih, classical.some $ this (ordinal.sup.{u u} (λ x : ρ.out.α × subtype (< μ), max α₀ $
    ι $ nr (ih x.2.val x.2.2) x.1)) (_)),
  let A2 := range (subtype.val ∘ pick),
  have h1A2 : mk A2 = θ, sorry,
  let sub_α₀ : set θ.ord.out.α := ι ⁻¹' {c | c ≤ α₀ },
  have h2A2 : ∀(x ∈ A2) (y ∈ A2), x ≠ y → x ∩ y ⊆ sub_α₀, sorry,
  have : ∃r B, r ⊆ sub_α₀ ∧ B ⊆ A2 ∧ mk B = θ ∧ ∀(x ∈ B), x ∩ sub_α₀ = r, sorry,
  { rcases this with ⟨r, B, hr, h1B, h2B, h3B⟩,
    refine ⟨B, subset.trans h1B _, h2B, r, _⟩, rw [range_subset_iff], intro x, exact (pick x).2,
    intros x y hx hy hxy, rw [←h3B x hx], apply set.ext, intro z, split,
    intro hz, refine ⟨hz.1, h2A2 x (h1B hx) y (h1B hy) hxy hz⟩,
    intro hz, refine ⟨hz.1, _⟩, rw [h3B x hx, ←h3B y hy] at hz, exact hz.1 },
  sorry
end
#exit
#print sup_lt_of_is_regular
#print sup_ord

lemma delta_system_lemma_1 (κ : cardinal) (hκ : cardinal.omega ≤ κ) {θ} (hκθ : κ < θ)
  (hθ : is_regular θ) (hθ_le : ∀(α < θ.ord), card (powerlt α κ.ord) < θ)
  (A : set (set (θ.ord.out.α)))
  (hA : mk (subtype A) = θ) (hA2 : ∀(x ∈ A), mk (subtype x) < κ) :
  ∃(B ⊆ A), mk B = θ ∧ is_delta_system B :=
begin
  sorry
end
/-- The delta-system lemma. [Kunen 1980, Theorem 1.6, p49] -/
theorem delta_system_lemma {α : Type u} (κ : cardinal) (hκ : cardinal.omega ≤ κ) {θ} (hκθ : κ < θ)
  (hθ : is_regular θ) (hθ_le : ∀(α < θ.ord), card (powerlt α κ.ord) < θ) (A : set (set α))
  (hA : θ ≤ mk A) (hA2 : ∀(x ∈ A), mk (subtype x) < κ) :
  ∃(B ⊆ A), mk B = θ ∧ is_delta_system B :=
begin
  sorry
end


end delta_system

namespace topological_space

variables {α : Type u} [topological_space α]

def open_set (α : Type u) [topological_space α] : Type u := subtype (@_root_.is_open α _)

def countable_chain_condition : Prop :=
∀(s : set $ open_set α), pairwise (disjoint on s) → s.countable



end topological_space