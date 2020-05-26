/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
import .to_mathlib .pSet_ordinal data.pfun
-- local attribute [instance] classical.prop_decidable

/- The Cohen poset of finite partial functions (2^(2^ω)) × ω → 2 -/

/- The underlying type of the Cohen poset is the type of finite partial functions from (set $ set ω) × ω → Prop -/
variable {η : cardinal}

def cohen_poset := {f : ((pSet.ordinal.mk η.ord).type × ℕ) →. Prop | set.finite (pfun.dom f)}

-- TODO replace all instances of set $ set ℕ with a generic "B"
noncomputable instance B_decidable_eq : decidable_eq (set $ set ℕ) := λ _ _, classical.prop_decidable _

namespace pfun
/- Two partial functions are equal if their graphs are equal -/
lemma ext_graph {α β : Type*} (f g : α →. β) (h_graph : f.graph = g.graph) : f = g :=
  pfun.ext $ λ _ _, iff_of_eq (congr_fun h_graph (_,_))

lemma graph_empty_iff_dom_empty {α β : Type*} (f : α →. β) : f.graph = ∅ ↔ f.dom = ∅ :=
begin
  have := dom_iff_graph f,
  split; intro; ext; safe, apply this, tidy
end

/- A functional graph is a univalent graph -/
def functional {α β : Type*} (Γ : set (α × β)) : Prop :=
  ∀ a b₁ b₂, (a, b₁) ∈ Γ → (a, b₂) ∈ Γ → b₁ = b₂

lemma congr_arg {α β : Type*} (f : α →. β) : ∀ {x} {y} (h₁ : x ∈ f.dom) (h₂ : y ∈ f.dom)
  (h_eq : x = y), fn f x h₁ = fn f y h₂ :=
by intros; congr; assumption

lemma functional_subset {α β : Type*} (Γ Γ': set (α × β)) (h_Γ' : Γ' ⊆ Γ) (h_Γ : functional Γ) : functional Γ' :=
  λ _ _ _ _ _, by apply h_Γ; tidy

/-- The graph of a pfun is always functional -/
lemma graph_functional {α β : Type*} (f : α →. β) : functional f.graph := by tidy

/-- Given a partial functional relation, turn it into a pfun -/
noncomputable def of_graph {α β : Type*} (Γ : set (α × β)) (h_Γ : functional Γ) : α →. β :=
  λ a, ⟨∃ c ∈ Γ, (prod.fst c) = a, λ h, @prod.snd α β $ (classical.indefinite_description _ h).val⟩

lemma of_graph_property {α β : Type*} (Γ : set $ α × β) (h_Γ : functional Γ) (a : α) (h : ∃ c ∈ Γ, (prod.fst c) = a) : ∃ (H : Γ (classical.indefinite_description _ h)), (classical.indefinite_description _ h).val.fst = a :=
  by apply (classical.indefinite_description _ h).property

lemma of_graph_get {α β : Type*} (Γ : set $ α × β) (h_Γ : functional Γ) (a : α) : ∀ h,
(of_graph Γ h_Γ a).get h = (classical.indefinite_description _ h).val.snd :=
  by intro; refl

lemma of_graph_val {α β : Type*} (Γ : set $ α × β) (h_Γ : functional Γ) (a : α) (h : ∃ c ∈ Γ, (prod.fst c) = a) (c' ∈ Γ) (h' : c'.1 = a) :
  @prod.snd α β (classical.indefinite_description _ h).val = c'.snd :=
begin
  let c'', swap, change (prod.snd c'' = c'.snd),
  apply h_Γ a, swap, convert H, ext, rwa[h'], refl,
  have := (classical.indefinite_description _ h).property,
  cases this with this1 this2, rw[<-this2], convert this1, ext; refl
end

@[simp]lemma graph_of_graph {α β : Type*} (Γ : set $ α × β) (h_Γ : functional Γ) : (of_graph Γ h_Γ).graph = Γ :=
begin
  ext, rcases x with ⟨a,b⟩, dsimp[graph],
  split; intro H, {cases H, induction H_h, cases H_w, cases H_w_h, induction H_w_h_h,
  convert H_w_h_w, ext, refl, rw[of_graph_get], apply of_graph_val; try{assumption}; refl},
  fsplit, {tidy}, rw[of_graph_get], apply @of_graph_val _ _ Γ _ a _ (a,b) _;
  try{assumption}; refl
end

@[simp]lemma of_graph_graph {α β : Type*} {f : α →. β} : of_graph (f.graph) (graph_functional f) = f :=
  by apply ext_graph; rw[graph_of_graph]

@[simp]lemma dom_of_graph {α β : Type*} (Γ : set $ α × β) (h_Γ : functional Γ) : (of_graph Γ h_Γ).dom = (prod.fst '' Γ) :=
begin
 ext, split; intros, {tidy},
 {cases a, cases a_h, cases a_w, induction a_h_right, dsimp at *, fsplit,
 work_on_goal 0 { fsplit }, work_on_goal 2 {fsplit,
 work_on_goal 0 { assumption }, refl }}
end

@[simp]lemma dom_of_graph_union {α β : Type*} (Γ : set $ α × β) (p : α × β) (h_Γ : functional Γ) (h_Γ' : functional $ Γ ∪ {p}) : (of_graph (Γ ∪ {p}) h_Γ').dom = (of_graph Γ h_Γ).dom ∪ {p.fst} :=
  by simp[dom_of_graph, set.image_insert_eq]

lemma in_dom_of_in_graph {α β : Type*} {f : α →. β} : ∀ {a} {b}, (a,b) ∈ f.graph → a ∈ f.dom :=
  by {intros a b H, apply (pfun.dom_iff_graph _ a).mpr, exact ⟨b,H⟩}

lemma lift_graph' {α β : Type*} {f : α →. β} {a : α} {b : β} (h_a : a ∈ f.dom) : (a,b) ∈ f.graph ↔ pfun.fn f a h_a = b := by tidy

end pfun

/- Partial order structure on the Cohen poset -/
instance partial_order_cohen_poset : partial_order (@cohen_poset η) :=
{ le := λ f g, g.val.graph ⊆ f.val.graph,
  lt := λ f g, g.val.graph ⊆ f.val.graph ∧ ¬ f.val.graph ⊆ g.val.graph,
  le_refl := λ _, by unfold has_le.le,
  le_trans := by {intros, apply set.subset.trans, exact a_2, assumption},
  lt_iff_le_not_le := λ _ _, iff.refl _,
  le_antisymm := λ a b h1 h2, by {have := @set.subset.antisymm _ _ _ h2 h1, cases a, cases b,
                                       congr, apply pfun.ext_graph, exact this}}

def incompatible {α : Type*} [partial_order α] (a b : α) := ¬ ∃ c, c ≤ a ∧ c ≤ b

def antichain {α : Type*} [partial_order α] (s : set α) := ∀ x ∈ s, ∀ y ∈ s, (x ≠ y) → incompatible x y

lemma antichain_subset {α : Type*} [partial_order α] {s s' : set α} {h : s' ⊆ s} {hs : antichain s} : antichain s' :=
by {intros _ _ _ _, intro H, apply hs _ _ _ _, tidy}

def countable_chain_condition (α : Type*) [partial_order α] := ∀ s : set α, antichain s → set.countable s

@[simp]lemma univ_singletons {α : Type*} :  set.Union (λ a, {a}) = (set.univ : set α) :=
by tidy

lemma set_is_union_of_fibers {α β : Type*} (f : α → β) (s : set α) : s = set.Union (λ b, f ⁻¹'{b} ∩ s) := by ext; simp

lemma univ_is_union_of_fibers {α β : Type*} (f : α → β) : @set.univ α = set.Union (λ b, f⁻¹' {b}) :=
  begin [smt] eblast_using [set.preimage_Union, @set.preimage_univ α β f, univ_singletons] end

lemma countable_of_injection_to_countable {α β : Type*} {s : set α} {s' : set β} (f : s → s') {hf : function.injective f} (h' : set.countable s') : set.countable s :=
begin
  have := set.countable_iff_exists_injective.mp h', apply set.countable_iff_exists_injective.mpr,
  cases this, refine ⟨this_w ∘ f,_⟩, exact function.injective.comp (this_h) hf
end

lemma countable_of_bijection_with_countable {α β : Type*} {s : set α} {s' : set β} {f : s → s'}
{hf : function.bijective f} {h' : set.countable s'} : set.countable s :=
begin
  apply countable_of_injection_to_countable f, exact h', exact hf.left
end

lemma countable_of_equiv_with_countable {α β : Type*} {s : set α} {s' : set β}
{h : equiv s s'} {h' : set.countable s'} : set.countable s :=
by {apply countable_of_bijection_with_countable, apply h.bijective, exact h'}

lemma equiv_set_set_univ {α : Type*} (s : set α) : equiv s (@set.univ s) :=
by {refine ⟨λ x, ⟨x, (by trivial)⟩, λ x, x.val, _, _⟩, tidy}

/- an (s : set α) is countable if (set.univ : set s) is countable -/
lemma countable_of_countable_univ {α : Type*} (s : set α) : set.countable s ↔ set.countable (set.univ : set s) :=
begin
  split; apply countable_of_equiv_with_countable, symmetry,
  all_goals{apply equiv_set_set_univ}
end

lemma countable_of_countable_underlying_set {α : Type*} {s' : set α} {s : set α} {t : set s'} (h : s = (subtype.val '' t)) {h_ctbl : set.countable s} : set.countable t :=
begin
  let f : t → s := λ x,
    begin refine ⟨x.val, _⟩, rw[h], cases x, cases x_val, simp at *, fsplit; assumption end,
  refine countable_of_injection_to_countable f (by assumption),
    intros a₁ a₂ a, cases a₂, cases a₁, cases a₁_val, cases a₂_val, simp at *, assumption
end

lemma countable_of_countable_fibers {α β : Type*} (s : set α) (f : s → β) [encodable β] (H : ∀ b : β, set.countable (f ⁻¹' {b})) : set.countable s :=
by simp[countable_of_countable_univ, univ_is_union_of_fibers f, set.countable_Union H]

lemma countable_of_countable_fibers' {α β : Type*} (s : set α) (f : α → β) [encodable β] (H : ∀ b : β, set.countable ((f ⁻¹' {b}) ∩ s)) : set.countable s :=
by {rw[set_is_union_of_fibers f s], exact set.countable_Union H}

lemma countable_of_countable_fibers'' {α β : Type*} (s : set α) (f : s → β) [encodable β] (H : ∀ b : β, set.countable ((f ⁻¹' {b}))) : set.countable s :=
by simp[countable_of_countable_univ, univ_is_union_of_fibers f, set.countable_Union H]

lemma eq_true_of_provable {p : Prop} (h : p) : (p = true) := by simp[h]

lemma eq_false_of_provable_neg {p : Prop} (h : ¬ p) : (p = false) := by finish

@[reducible, simp]noncomputable def Prop_to_bool (p : Prop) : bool :=
by {haveI := classical.prop_decidable p, by_cases p, exact true, exact false}

@[simp]lemma Prop_to_bool_true : Prop_to_bool true = tt := by simp

@[simp]lemma Prop_to_bool_false : Prop_to_bool false = ff := by simp

noncomputable lemma equiv_Prop_bool : equiv Prop bool :=
begin
  refine ⟨Prop_to_bool,by {intro b, cases b, exact false, exact true},_,_⟩,
  {unfold function.left_inverse, intro p, haveI := classical.prop_decidable p, by_cases p,
  rw[eq_true_of_provable h, Prop_to_bool_true],
  rw[eq_false_of_provable_neg h, Prop_to_bool_false],},
  {intro x, cases x; finish}
end

noncomputable instance Prop_encodable : encodable Prop :=
 @encodable.of_equiv _ _ (by apply_instance) equiv_Prop_bool

noncomputable def size_of_domain : (@cohen_poset η) → ℕ :=
  λ p, finset.card $ set.finite.to_finset p.property

lemma size_of_domain_fiber {n} {p : @cohen_poset η} (h : p ∈ @size_of_domain η ⁻¹' {n}) : size_of_domain p = n := by finish

/-- The partial function p is defined at b and m if (b,m) is in the domain of p -/
def is_defined (p : (@cohen_poset η)) (b) (m) := (b,m) ∈ (pfun.dom p.val)

/-- p is defined at m if there exists a b such that p is defined at b and m -/
def is_defined_at (m : ℕ) : set (@cohen_poset η) :=
  {p : (@cohen_poset η) | ∃ b, is_defined p b m}

namespace finset

lemma empty_of_empty {α : Type*} {s : set α} {h : set.finite s} : set.finite.to_finset h = ∅ → s = ∅ :=
begin
  intro H, rw[set.eq_empty_iff_forall_not_mem], intros x Hx,
  suffices : x ∈ set.finite.to_finset h, by rw[H] at this; cases this, simpa[finset.mem_coe]
end

end finset

lemma empty_of_size_of_domain_0 {p : (@cohen_poset η)} (h : size_of_domain p = 0) : p.val.dom = ∅ :=
begin
  have : set.finite.to_finset p.property = ∅, from finset.card_eq_zero.mp h,
  exact finset.empty_of_empty this
end

lemma nonempty_of_size_of_domain_ne_zero {p : (@cohen_poset η)} (h : size_of_domain p ≠ 0) : nonempty p.val.dom :=
begin
  have : set.finite.to_finset p.property ≠ ∅, by {intro h, suffices : (set.finite.to_finset p.property).card = 0,
    by {apply (_root_.not_and_self ((set.finite.to_finset p.property).card = 0)).mp,refine ⟨(by assumption), this⟩},
    exact finset.card_eq_zero.mpr h},
  have := finset.exists_mem_of_ne_empty this, cases this, apply nonempty.intro,
  refine ⟨this_w,_⟩, cases this_w, cases p, simp at this_h, assumption
end

lemma nonempty_domain_defined (p : (@cohen_poset η)) (h : 0 < size_of_domain p) : ∃ m,
  is_defined_at m p :=
begin
  suffices : nonempty p.val.dom, by {have := classical.choice this, cases this,
  refine ⟨this_val.2, ⟨this_val.1,_⟩⟩, tidy}, apply nonempty_of_size_of_domain_ne_zero,
  intro h', rw[h'] at h, cases h
end

-- def is_defined_at_covers {n} {h : 0 < n} : @size_of_domain η ⁻¹' {n} ⊆ ⋃ m, is_defined_at m :=
-- begin
--   intros p Hp, simp[set.mem_preimage_eq] at *,
--   suffices : nonempty p.val.dom,
--     by {have := classical.choice this, exact ⟨this.val.snd, ⟨this.val.fst, (by tidy)⟩⟩},
--   apply nonempty_of_size_of_domain_ne_zero, intro H, have : 0 < 0, by cc, cases this
-- end

instance size_of_domain_0_subsingleton : subsingleton $ @size_of_domain η ⁻¹' {0} :=
begin
  refine ⟨λ a b, _⟩, rcases a with ⟨⟨p_a, H_f_a⟩, H_a⟩, rcases b with ⟨⟨p_b, H_f_b⟩, H_b⟩, congr,
  have := (pfun.graph_empty_iff_dom_empty _).mpr (@empty_of_size_of_domain_0 η _
                                          (by {simp[set.mem_preimage_eq] at H_b, exact H_b})),
  have := (pfun.graph_empty_iff_dom_empty _).mpr (@empty_of_size_of_domain_0 η _
                                          (by {simp[set.mem_preimage_eq] at H_a, exact H_a})),
  exact pfun.ext_graph _ _ (by cc)
end

lemma subsingleton_of_subset_of_subsingleton {α : Type*} {s s' : set α} (h_sub : s ⊆ s') [subsingleton s'] : subsingleton s :=
begin
  refine ⟨λ a b, _⟩, have : ∀ a b : s', a = b, by apply subsingleton.elim,
  let f : s → s' := λ x, ⟨x.val, h_sub _⟩,
  suffices : f a = f b, by tidy, apply this, exact x.property
end

lemma size_of_domain_0_inter_subsingleton : ∀ (a : set (@cohen_poset η)), subsingleton ↥((size_of_domain ⁻¹' {0}) ∩ a) :=
λ a, subsingleton_of_subset_of_subsingleton
     (by apply set.inter_subset_left : size_of_domain ⁻¹' {0} ∩ a ⊆ size_of_domain ⁻¹' {0})

lemma countable_subsingleton {α : Type*} (s : set α) (h : subsingleton s) : set.countable s :=
  set.countable_iff_exists_injective.mpr $ ⟨λ _, 0, λ _ _, dec_trivial⟩

-- lemma cover_Union_eq {α ι : Type*} {s : set α} {t : ι → set α} {h : s ⊆ (⋃ (i : ι), t i)} :
-- s = ⋃ i, s ∩ t i :=
--   by {rw[<-set.inter_Union_left], ext, split; intros, exact ⟨a, h a⟩, exact a.left}

lemma inter_subset_left' {α : Type*} {s t u : set α} {h : t ⊆ u} : s ∩ t ⊆ u :=
  λ _ ⟨_,_⟩, by solve_by_elim

lemma inter_subset_right' {α : Type*} {s t u : set α} {h : t ⊆ u} : t ∩ s ⊆ u :=
  λ _ ⟨_,_⟩, by solve_by_elim

section one_point_restriction

/- Given x : α, return the set λ a, a ≠ x -/
@[simp, reducible]def not_x {α : Type*} (x : α) : set α := λ a, a ≠ x

def finite_of_inter_not_x {α : Type*} {s : set α} (h : set.finite s) {x : α} : set.finite $ s ∩ not_x x := by {apply set.finite_subset, exact h, apply inter_subset_right', trivial}

def roption_indicator {α : Type*} (s : set α) : α → roption α :=
  λ x, ⟨x ∈ s, λ _, x⟩

def pfun.restriction {α β : Type*} (f : α →. β) (s : set α) : α →. β
:= λ x, do y <- roption_indicator s x, f y

lemma pfun.domain_restriction {α β : Type*} {f : α →. β} {s : set α} : (pfun.restriction f s).dom = f.dom ∩ s :=
  by ext; split; intro a; cases a; fsplit; assumption

end one_point_restriction
-- def one_point_restriction (p : (@cohen_poset η)) : ∀(x), x ∈ p.val.dom → (@cohen_poset η) :=
-- λ x H, ⟨pfun.restriction p.val (not_x x),
--          by {change set.finite (pfun.restriction p.val (not_x x)).dom,
--          rw[pfun.domain_restriction], apply finite_of_inter_not_x, apply p.property}⟩

-- def one_point_restriction' (p : (@cohen_poset η)) : ∀ (x), (@cohen_poset η) :=
-- λ x, ⟨pfun.restriction p.val (not_x x),
--          by {change set.finite (pfun.restriction p.val (not_x x)).dom,
--          rw[pfun.domain_restriction], apply finite_of_inter_not_x, apply p.property}⟩

-- lemma one_point_restriction_domain {p : (@cohen_poset η)} {x} (h : x ∈ p.val.dom) : (one_point_restriction p x h).val.dom = p.val.dom ∩ not_x x :=
-- begin
--   ext, split; {intros a, auto_cases, fsplit; assumption}
-- end

-- lemma one_point_restriction_domain' {p : (@cohen_poset η)} {x} : (one_point_restriction' p x).val.dom = p.val.dom ∩ not_x x :=
-- begin
--   ext, split; {intros a, auto_cases, fsplit; assumption}
-- end

-- lemma one_point_restriction_graph {p : (@cohen_poset η)} {x} {h_x : x ∈ p.val.dom} : ∀ y, y ∈ (one_point_restriction p x h_x).val.graph ↔ (y ∈ p.val.graph ∧ (prod.fst y ≠ x)) := sorry

-- -- lemma one_point_restriction_graph' {p : (@cohen_poset η)} {x} : (one_point_restriction' p x).val.graph = {y ∈ p.val.graph | y.fst ∈ not_x x} :=
-- -- begin
-- --   ext, split; intros,
-- -- end

-- @[simp]lemma in_one_point_restriction_of_in_dom_and_not_x {p : (@cohen_poset η)} {x} {h : x ∈ p.val.dom} {y} : y ∈ (one_point_restriction p x h).val.dom ↔ (y ∈ p.val.dom) ∧ y ≠ x :=
--   by simp[one_point_restriction_domain, not_x]; finish

-- @[simp]lemma in_one_point_restriction'_of_in_dom_and_not_x {p : (@cohen_poset η)} {x} {y} : y ∈ (one_point_restriction' p x ).val.dom ↔ (y ∈ p.val.dom) ∧ y ≠ x :=
--   by simp[one_point_restriction_domain', not_x]; finish

-- lemma one_point_restriction_domain'_subset {p : (@cohen_poset η)} {x} : (one_point_restriction' p x).val.dom ⊆ p.val.dom :=
--   λ y, by finish

-- lemma one_point_restriction_domain_subset {p : (@cohen_poset η)} {x} {h_x : x ∈ p.val.dom} : (one_point_restriction p x h_x).val.dom ⊆ p.val.dom :=
--   λ y, by finish


-- lemma one_point_restriction_domain_coe {p : (@cohen_poset η)} {x} {h : x ∈ p.val.dom} : p.val.dom = ↑(set.finite.to_finset p.property) := by simp

-- lemma one_point_restriction_finset_rewrite {p : (@cohen_poset η)} {x} {h : x ∈ p.val.dom} : set.finite.to_finset (one_point_restriction p x h).property = set.finite.to_finset (by {apply finite_of_inter_not_x, exact p.property} : set.finite $ p.val.dom ∩ not_x x) := by simp[one_point_restriction_domain]

-- lemma one_point_restriction_finset_rewrite_property {p : (@cohen_poset η)} {x} {h : x ∈ p.val.dom} : ∀ y, y ∈ set.finite.to_finset ((one_point_restriction p x h).property-- by {apply finite_of_inter_not_x, exact p.property} : set.finite $ p.val.dom ∩ not_x x
-- ) ↔ y ≠ x ∧ y ∈ p.val.dom :=
-- begin
--   intro y, split; intros, rw[one_point_restriction_finset_rewrite] at a, split,
--     {tidy, apply a_right, refl},
--     {finish},
--     {apply finset.mem_coe.mp, rw[<-one_point_restriction_domain_coe],
--     rw[one_point_restriction_domain], refine ⟨a.right,_⟩, apply a.left, swap, exact y, simp*}
-- end

-- lemma one_point_restriction_erase {p : (@cohen_poset η)} {x} {h : x ∈ p.val.dom} : set.finite.to_finset (one_point_restriction p x h).property = finset.erase (set.finite.to_finset p.property) x :=
-- begin
--   ext, rw[one_point_restriction_finset_rewrite,finset.mem_erase], conv {to_rhs,rw[<-finset.mem_coe]}, split; intros, {rw[<-one_point_restriction_domain_coe], apply (one_point_restriction_finset_rewrite_property a).mp, show set (set ℕ) × ℕ, exact x, rw[one_point_restriction_finset_rewrite], repeat{assumption}},
--   {rw[<-one_point_restriction_finset_rewrite],
--   apply (one_point_restriction_finset_rewrite_property a).mpr,
--   convert a_1, simp, assumption}
-- end

-- lemma one_point_restriction_decrease_size {n} (p : (@cohen_poset η)) (h : size_of_domain p = n + 1) (x) (h_x : x ∈ p.val.dom)  :
-- size_of_domain (one_point_restriction p x h_x) = n :=
-- begin
--   unfold size_of_domain at *, have : n = nat.pred (n+1), by refl,
--   rw[this, one_point_restriction_erase, <-h], apply finset.card_erase_of_mem,
--   apply finset.mem_coe.mp, rwa[finset.coe_to_finset]
-- end

-- def aux_c'' {p₁ p₂ : (@cohen_poset η)} {t₁ t₂ : (set $ set ℕ) × ℕ} (h_t₁ : t₁ ∈ p₁.val.dom) (h_t₂ : t₂ ∈ p₂.val.dom) (q : Prop) (h_val₁ : pfun.fn p₁.val t₁ h_t₁ = q) (h_val₂ : pfun.fn p₂.val t₂ h_t₂ = q) (c : (@cohen_poset η)) : (@cohen_poset η) :=
--   (one_point_restriction' (one_point_restriction' c t₁) t₂)

-- lemma aux_c''_dom {p₁ p₂ : (@cohen_poset η)} {t₁ t₂ : (set $ set ℕ) × ℕ} {h_t₁ : t₁ ∈ p₁.val.dom} {h_t₂ : t₂ ∈ p₂.val.dom} {q : Prop} {h_val₁ : pfun.fn p₁.val t₁ h_t₁ = q} {h_val₂ : pfun.fn p₂.val t₂ h_t₂ = q} {c : (@cohen_poset η)} : ∀ (x), x ∈ (aux_c'' h_t₁ h_t₂ q h_val₁ h_val₂ c).val.dom → x ≠ t₁ ∧ x ≠ t₂ :=
-- λ x Hx, ⟨by {apply ((in_one_point_restriction'_of_in_dom_and_not_x).mp _).right, exact c,
--             apply one_point_restriction_domain'_subset, swap, exact t₂, exact Hx},
--          by {apply ((in_one_point_restriction'_of_in_dom_and_not_x).mp _).right, exact (one_point_restriction' c t₁), exact Hx}⟩

-- lemma aux_c''_dom_of {p₁ p₂ : (@cohen_poset η)} {t₁ t₂ : (set $ set ℕ) × ℕ} {h_t₁ : t₁ ∈ p₁.val.dom} {h_t₂ : t₂ ∈ p₂.val.dom} {q : Prop} {h_val₁ : pfun.fn p₁.val t₁ h_t₁ = q} {h_val₂ : pfun.fn p₂.val t₂ h_t₂ = q} {c : (@cohen_poset η)} : ∀ (x), x ≠ t₁ ∧ x ≠ t₂ → x ∈ c.val.dom → x ∈ (aux_c'' h_t₁ h_t₂ q h_val₁ h_val₂ c).val.dom :=
-- begin
--   intros x Hx H'x, rcases Hx with ⟨Hx_r, Hx_l⟩, dsimp[aux_c''],
--   repeat{rw[one_point_restriction_domain']}, finish
-- end

-- lemma aux_c''_graph_of {p₁ p₂ : (@cohen_poset η)} {t₁ t₂ : (set $ set ℕ) × ℕ} {h_t₁ : t₁ ∈ p₁.val.dom} {h_t₂ : t₂ ∈ p₂.val.dom} {q : Prop} {h_val₁ : pfun.fn p₁.val t₁ h_t₁ = q} {h_val₂ : pfun.fn p₂.val t₂ h_t₂ = q} {c : (@cohen_poset η)} : ∀ x, (x ∈ c.val.graph ∧ (prod.fst x ≠ t₁ ) ∧ (prod.fst x ≠ t₂)) ↔ x ∈ (aux_c'' h_t₁ h_t₂ q h_val₁ h_val₂ c).val.graph := sorry

-- lemma aux_c''_dom_finite {p₁ p₂ : (@cohen_poset η)} {t₁ t₂ : (set $ set ℕ) × ℕ} {h_t₁ : t₁ ∈ p₁.val.dom} {h_t₂ : t₂ ∈ p₂.val.dom} {q : Prop} {h_val₁ : pfun.fn p₁.val t₁ h_t₁ = q} {h_val₂ : pfun.fn p₂.val t₂ h_t₂ = q} {c : (@cohen_poset η)} : set.finite (aux_c'' h_t₁ h_t₂ q h_val₁ h_val₂ c).val.dom :=
-- begin
--   dsimp[aux_c''], repeat{rw[one_point_restriction_domain']}, repeat{apply finite_of_inter_not_x},
--   exact c.property
-- end
-- -- λ x Hx, ⟨by {apply ((in_one_point_restriction'_of_in_dom_and_not_x).mp _).right, exact c,
-- --             apply one_point_restriction_domain'_subset, swap, exact t₂, exact Hx},
-- --          by {apply ((in_one_point_restriction'_of_in_dom_and_not_x).mp _).right, exact (one_point_restriction' c t₁), exact Hx}⟩

-- /- Let p₁ and p₂ be two partial functions such that there is a point (b₁,m) for p₁ and a point (b₂, m) for p₂ where p₁ and p₂ have the same value.
--     Suppose that the one-point restrictions of p₁ and p₂ with respect to (b₁,m) and (b₂,m) have a common refinement c.
--     Then c (after making sure (b₁, m) and (b₂,m) are not in its domain) extended by (b₁,m) and (b₂,m) is a common refinement for p₁ and p₂. -/

-- /-- the graph of the extension of c by (b₁,m) and (b₂,m) -/
-- def one_point_restriction_refinement_extension_graph {p₁ p₂ : (@cohen_poset η)} {t₁ t₂ : (set $ set ℕ) × ℕ} (h_t₁ : t₁ ∈ p₁.val.dom) (h_t₂ : t₂ ∈ p₂.val.dom) (q : Prop) (h_val₁ : pfun.fn p₁.val t₁ h_t₁ = q) (h_val₂ : pfun.fn p₂.val t₂ h_t₂ = q) (c : (@cohen_poset η)) :=
--   ((aux_c'' h_t₁ h_t₂ q h_val₁ h_val₂ c).val.graph ∪ {(t₁,q)} ∪ {(t₂,q)})

-- lemma one_point_restriction_refinement_extension_graph_functional {p₁ p₂ : (@cohen_poset η)} {t₁ t₂ : (set $ set ℕ) × ℕ} (h_t₁ : t₁ ∈ p₁.val.dom) (h_t₂ : t₂ ∈ p₂.val.dom) (q : Prop) (h_val₁ : pfun.fn p₁.val t₁ h_t₁ = q) (h_val₂ : pfun.fn p₂.val t₂ h_t₂ = q) (c : (@cohen_poset η)) (h_c_left : c ≤ (one_point_restriction p₁ t₁ h_t₁)) (h_c_right : c ≤ (one_point_restriction p₂ t₂ h_t₂)) :
--   pfun.functional $ one_point_restriction_refinement_extension_graph h_t₁ h_t₂ q h_val₁ h_val₂ c :=
-- begin
--   intros x q₁ q₂ H₁ H₂, let c' := (aux_c'' h_t₁ h_t₂ q h_val₁ h_val₂ c), cases H₁; cases H₂; cases H₁; cases H₂,
--   apply pfun.graph_functional (aux_c'' h_t₁ h_t₂ q h_val₁ h_val₂ c).val, exact H₁, exact H₂,
--   {have : x ∈ c'.val.dom,
--     by {apply (pfun.dom_iff_graph c'.val x).mpr, exact ⟨q₁, H₁⟩}, have := (aux_c''_dom x this).left, suffices : x = t₁, by contradiction, repeat{cases H₂}, refl},
--   {repeat{cases H₁}, suffices : t₁ ≠ t₁, by contradiction, have : t₁ ∈ c'.val.dom,
--    by {apply (pfun.dom_iff_graph c'.val t₁).mpr, exact ⟨q₂, H₂⟩},
--    exact (aux_c''_dom t₁ this).left},
--   {cases H₁; cases H₁; cases H₂; cases H₂, cc},
--   {repeat{cases H₂}, suffices : t₂ ≠ t₂, by contradiction, have : t₂ ∈ c'.val.dom,
--    by {apply (pfun.dom_iff_graph c'.val t₂).mpr, exact ⟨q₁, H₁⟩},
--    exact (aux_c''_dom t₂ this).right},
--   {cases H₂},
--   {repeat{cases H₁}, cases H₂, refl},
--   {cases H₂},
--   {repeat{cases H₁}, suffices : t₂ ≠ t₂, by contradiction, have : t₂ ∈ c'.val.dom,
--    by {apply (pfun.dom_iff_graph c'.val t₂).mpr, refine ⟨_,_⟩, exact q₂, exact H₂},
--    exact (aux_c''_dom t₂ this).right}, {repeat{cases H₂}, cases H₁, refl},
--   {cases H₁}, {cases H₁}, {cc}, {cases H₂}, {cases H₁}, {cases H₁},
-- end

-- /-- the graph of the extension of c by (b₁,m) and (b₂,m) contains the graphs of p₁ and p₂ -/
-- lemma one_point_restriction_refinement_extension_graph_extends {p₁ p₂ : (@cohen_poset η)} {t₁ t₂ : (set $ set ℕ) × ℕ} (h_t₁ : t₁ ∈ p₁.val.dom) (h_t₂ : t₂ ∈ p₂.val.dom) (q : Prop) (h_val₁ : pfun.fn p₁.val t₁ h_t₁ = q) (h_val₂ : pfun.fn p₂.val t₂ h_t₂ = q) (c : (@cohen_poset η)) (h_c_left : c ≤ (one_point_restriction p₁ t₁ h_t₁)) (h_c_right : c ≤ (one_point_restriction p₂ t₂ h_t₂)) : p₁.val.graph ⊆ (one_point_restriction_refinement_extension_graph h_t₁ h_t₂ q h_val₁ h_val₂ c) ∧ p₂.val.graph ⊆ (one_point_restriction_refinement_extension_graph h_t₁ h_t₂ q h_val₁ h_val₂ c) :=
-- begin
--   split; intros x Hx; rcases x with ⟨x, q'⟩;
--   dsimp[one_point_restriction_refinement_extension_graph],
--   suffices : ((x, q') ∈ pfun.graph ((aux_c'' h_t₁ h_t₂ q h_val₁ h_val₂ c).val)) ∨ ((x, q') ∈ {(t₁, q)} ∨
--     (x, q') ∈ {(t₂, q)}), by rwa[or_assoc],
--   let H, swap, change _ ∨ H, haveI : decidable H := by apply classical.prop_decidable _,
--   by_cases H,
--     {apply or.elim h, exact λ A, or.inr $ or.inl $ A,
--                       exact λ A, or.inr $ or.inr $ A},
--     {-- dsimp[H] at h, rw[not_or_distrib] at h, apply or.inl,
--     repeat{sorry}

--     -- apply (aux_c''_graph_of (x,q')).mp,
--      -- refine ⟨_, _⟩,

-- -- dsimp[H] at h, rw[not_or_distrib] at h,
-- --      have Hx' : (x,q') ∈ (c.val).graph,
-- --        by {apply h_c_left, apply (one_point_restriction_graph (x,q')).mpr,
-- --        refine ⟨(by assumption), _⟩, change x ≠ t₁, cases h, intro hx, apply h_left, rw[hx], simp,
-- --               apply (pfun.graph_functional p₁.val), exact Hx,
-- --               rw[hx], apply (pfun.lift_graph' _).mpr, exact h_val₁},
-- --      apply or.inl, have : x ∈ p₁.val.dom, by apply (pfun.dom_iff_graph _ x).mpr; exact ⟨q', Hx⟩,
-- --      have : x ∈ ((aux_c'' h_t₁ h_t₂ q h_val₁ h_val₂ c).val).dom,
-- --        by {apply aux_c''_dom_of, {split, {change x ≠ t₁, cases h, intro hx,
-- --           apply h_left, rw[hx], simp, apply (pfun.graph_functional p₁.val), exact Hx,
-- --           rw[hx], apply (pfun.lift_graph' _).mpr, exact h_val₁}, {change x ≠ t₂, cases h, intro hx, apply h_right, rw[hx], simp, apply (pfun.graph_functional p₂.val), repeat{sorry} -- exact Hx, rw[hx], apply (pfun.lift_graph' _).mpr, exact h_val₂
-- --               }}, {apply (pfun.dom_iff_graph _ x).mpr, exact ⟨q', Hx'⟩}},

--     },
--   -- by_cases H, repeat{sorry}
--   -- have : ((x, q') ∈ {(t₁, q)} ∨ (x, q') ∈ {(t₂, q)}) → (x,q') ∉ pfun.graph ((aux_c'' h_t₁ h_t₂ q h_val₁ h_val₂ c).val),
--   -- by {intros H₁ H₂, have : x ∈ (aux_c'' h_t₁ h_t₂ q h_val₁ h_val₂ c).val.dom,
--   --    by {apply (pfun.dom_iff_graph _ x).mpr, exact ⟨q', H₂⟩}, have := aux_c''_dom x this,
--   --    cases H₁, have : (x,q') = (t₁, q), from set.eq_of_mem_singleton (by assumption), finish,
--   --    have : (x,q') = (t₂, q), from set.eq_of_mem_singleton (by assumption), finish},
--   repeat{sorry}

-- end

-- /-- the extension of c by (b₁, m) and (b₂,m) has finite domain -/
-- lemma one_point_restriction_refinement_extension_finite {p₁ p₂ : (@cohen_poset η)} {t₁ t₂ : (set $ set ℕ) × ℕ} (h_t₁ : t₁ ∈ p₁.val.dom) (h_t₂ : t₂ ∈ p₂.val.dom) (q : Prop) (h_val₁ : pfun.fn p₁.val t₁ h_t₁ = q) (h_val₂ : pfun.fn p₂.val t₂ h_t₂ = q) (c : (@cohen_poset η)) (h_c_left : c ≤ (one_point_restriction p₁ t₁ h_t₁)) (h_c_right : c ≤ (one_point_restriction p₂ t₂ h_t₂)) : set.finite (pfun.of_graph (one_point_restriction_refinement_extension_graph h_t₁ h_t₂ q h_val₁ h_val₂ c) (by {apply one_point_restriction_refinement_extension_graph_functional, repeat{assumption}})).dom :=
-- begin
--   unfold one_point_restriction_refinement_extension_graph,
--   rw[pfun.dom_of_graph_union], swap,
--   apply pfun.functional_subset (one_point_restriction_refinement_extension_graph h_t₁ h_t₂ q h_val₁ h_val₂ c),
--     by {unfold one_point_restriction_refinement_extension_graph, finish},
--   apply one_point_restriction_refinement_extension_graph_functional, repeat{assumption},
--   rw[pfun.dom_of_graph_union, pfun.of_graph_graph], simp only [set.union_singleton], repeat{apply set.finite_insert}, apply aux_c''_dom_finite
-- end

-- noncomputable def one_point_restriction_refinement_extension {p₁ p₂ : (@cohen_poset η)} {t₁ t₂ : (set $ set ℕ) × ℕ} (h_t₁ : t₁ ∈ p₁.val.dom) (h_t₂ : t₂ ∈ p₂.val.dom) (q : Prop) (h_val₁ : pfun.fn p₁.val t₁ h_t₁ = q) (h_val₂ : pfun.fn p₂.val t₂ h_t₂ = q) (c : (@cohen_poset η)) (h_c_left : c ≤ (one_point_restriction p₁ t₁ h_t₁)) (h_c_right : c ≤ (one_point_restriction p₂ t₂ h_t₂)) : (@cohen_poset η) :=
--   ⟨pfun.of_graph (one_point_restriction_refinement_extension_graph h_t₁ h_t₂ q h_val₁ h_val₂ c) (by {apply one_point_restriction_refinement_extension_graph_functional, repeat{assumption}}),
--    (by {apply one_point_restriction_refinement_extension_finite, repeat{assumption}})⟩

-- lemma one_point_restriction_refinement_extension_spec (p₁ p₂ : (@cohen_poset η)) {t₁ t₂ : (set $ set ℕ) × ℕ} {h_t₁ : t₁ ∈ p₁.val.dom} {h_t₂ : t₂ ∈ p₂.val.dom} {q : Prop} {h_val₁ : pfun.fn p₁.val t₁ h_t₁ = q} {h_val₂ : pfun.fn p₂.val t₂ h_t₂ = q} {c : (@cohen_poset η)} (h_c_left : c ≤ (one_point_restriction p₁ t₁ h_t₁)) (h_c_right : c ≤ (one_point_restriction p₂ t₂ h_t₂)) : ∃ c' : (@cohen_poset η), c' ≤ p₁ ∧ c' ≤ p₂ :=
-- begin
--   refine ⟨by {fapply one_point_restriction_refinement_extension h_t₁ h_t₂ q h_val₁ h_val₂ c,
--              repeat{assumption}}, _⟩,
--   have := one_point_restriction_refinement_extension_graph_extends h_t₁ h_t₂ q h_val₁ h_val₂ c h_c_left h_c_right,
--   convert this; convert rfl; simp[one_point_restriction_refinement_extension, one_point_restriction_refinement_extension_graph, pfun.graph_of_graph]
-- end

-- lemma wit_incompatible {p₁ p₂ : (@cohen_poset η)} (h_incompat : incompatible p₁ p₂) : ∃ w ∈ p₁.val.dom ∩ p₂.val.dom, pfun.fn (p₁.val) w (by exact H.left) ≠ pfun.fn (p₂.val) w H.right :=
-- begin
--   sorry
--   -- let p, swap, change p, haveI : decidable p := by apply classical.prop_decidable _,
--   -- by_contra, dsimp[p] at a, clear _inst p,
--   -- simp at a, sorry
-- end

-- lemma wit_incompatible' {p₁ p₂ : (@cohen_poset η)} (h_incompat : incompatible p₁ p₂) : ∃ w q₁ q₂, (w,q₁) ∈ p₁.val.graph ∧ (w,q₂) ∈ p₂.val.graph ∧ q₁ ≠ q₂ := sorry

-- end one_point_restriction

-- lemma congr_neq {α β : Type*} {f : α → β} {x' y' : α} {x y : β} {h_x : f x' = x} {h_y : f y' = y} {h_neq : x ≠ y} : x' ≠ y' := λ _, by {cc}

-- lemma coe_subtype_injective {α : Type*} {s : set α} {x y : s} : (↑x = (↑y : α)) → x = y :=
--   λ h, by {cases x, cases y, dsimp at h, subst h}

-- -- /- The Cohen poset has the countable chain condition -/
-- -- lemma (@cohen_poset η)_ccc : countable_chain_condition (@cohen_poset η) :=
-- -- begin
-- --   intros a Ha, apply countable_of_countable_fibers' a size_of_domain,
-- --   intro n, induction n with n ih generalizing a,
-- --     {apply countable_subsingleton, apply size_of_domain_0_inter_subsingleton},
-- --     {let A_n, swap, change set.countable A_n,
-- --       have : A_n ⊆ ⋃ m, is_defined_at m, by {dsimp[A_n], apply inter_subset_right',
-- --              apply is_defined_at_covers, apply nat.zero_lt_succ},
-- --      rw[@cover_Union_eq _ _ A_n is_defined_at this], apply set.countable_Union,
-- --      intro m, let A_n_m, swap, change set.countable A_n_m,
-- --        have choice_aux : ∀ p : A_n_m, ∃ b : (set $ set ℕ), (b,m) ∈ (pfun.dom p.val.val),
-- --          by {intros p, cases p, cases p_property, cases p_val, assumption},
-- --        have := classical.axiom_of_choice choice_aux, cases this with wit wit_spec,
-- --        let eval : A_n_m → Prop :=
-- --              λ (p : ↥A_n_m), pfun.fn ((p.val).val) (wit p, m) (by apply wit_spec),
-- --        apply countable_of_countable_fibers'' _ eval, intro q,
-- --        let A_n_m_q, swap, change set.countable A_n_m_q,

-- --          let red : A_n_m → (@cohen_poset η) :=
-- --            λ X, one_point_restriction X.val (wit X, m) (by apply wit_spec),

-- --          have h_anti : antichain (red '' A_n_m_q) :=
-- --            by {intros x H_x y H_y H_neq H_compat, rcases H_compat with ⟨c, ⟨H_cx,H_cy⟩⟩,
-- --                rcases H_x with ⟨x', H_x'⟩, rcases H_y with ⟨y', H_y'⟩,
-- --                have h_neq : x' ≠ y',
-- --                  by {apply congr_neq, exact H_x'.right, exact H_y'.right, exact H_neq},
-- --                have : ↑x' ≠ ↑y', by {intro, apply h_neq, exact coe_subtype_injective a_1},
-- --                have h_incompat := Ha x' (x'.property.left.right) y' (y'.property.left.right) this,
-- --                have := wit_incompatible' h_incompat, rcases this with ⟨w,q₁,q₂, ⟨H₁,⟨H₂,H₃⟩⟩⟩,
-- --                have w_not_t₁ : w ≠ (wit (x'), m),
-- --                  by {intro H_eq, have := pfun.congr_arg (subtype.val (↑x'))
-- --                                          (pfun.in_dom_of_in_graph (by assumption))
-- --                                          (pfun.in_dom_of_in_graph (sorry)) H_eq, repeat{sorry}
-- --                      },
-- --                have w_not_t₂ : w.fst ≠ wit (y'), by sorry,
-- --                have w_in_red_1 : (w,q₁) ∈ (x).val.graph, by sorry,
-- --                have w_in_red_2 : (w,q₂) ∈ (y).val.graph, by sorry,
-- --                have w_in_c_1 : (w,q₁) ∈ c.val.graph, from H_cx w_in_red_1,
-- --                have w_in_c_2 : (w,q₂) ∈ c.val.graph, from H_cy w_in_red_2,
-- --                suffices : q₁ = q₂, by contradiction,
-- --                apply pfun.graph_functional c.val, exacts [w_in_c_1, w_in_c_2]
-- --                },

-- --          have ih_rewrite : size_of_domain ⁻¹' {n} ∩ red '' A_n_m_q = red '' A_n_m_q,
-- --            by {apply set.inter_eq_self_of_subset_right, intros x H_x,
-- --               simp only [set.mem_singleton_iff, set.mem_preimage_eq],
-- --               dsimp[red] at H_x, cases H_x, rw[<-H_x_h.right],
-- --               apply one_point_restriction_decrease_size,
-- --               apply size_of_domain_fiber H_x_w.property.left.left},

-- --          have h_inj : set.inj_on red A_n_m_q,
-- --            by {intros x' y' H_x' H_y',
-- --               haveI : decidable_eq ↥A_n_m := λ _ _, classical.prop_decidable _,
-- --               by_cases x' = y', exact λ _, ‹x' = y'›, rename h h_neq,
-- --               intro H, exfalso,
-- --                refine Ha x' (x'.property.left.right) y' (y'.property.left.right)
-- --                            (by {intro, apply h_neq, exact coe_subtype_injective a_1}) _,
-- --               apply one_point_restriction_refinement_extension_spec (↑x') (↑y'),
-- --               have : red x' ≤ red x', by {apply le_of_eq rfl},
-- --               convert this, convert (le_of_eq H), exact q,
-- --                cases H_x', convert H_x', cases H_x',
-- --                cases H_y', convert H_y', cases H_y'},

-- --          have ih' := ih (red '' A_n_m_q) h_anti,

-- --          exact set.countable_of_injective_of_countable_image h_inj (by rwa[<-ih_rewrite])}
-- end
