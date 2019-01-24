import .fol data.pfun data.set tactic.tidy data.set.countable data.set.basic .to_mathlib        

open fol

/- The Cohen poset of finite partial functions (2^(2^ω) × ω → 2 -/

/- The underlying type of the Cohen poset is the type of finite partial functions from (set $ set ω) × ω → Prop -/

def cohen_poset := {f : ((set $ set ℕ) × ℕ) →. Prop | set.finite (pfun.dom f)}

/- Two partial functions are equal if their graphs are equal -/
lemma ext_graph {α β : Type*} (f g : α →. β) (h_graph : f.graph = g.graph) : f = g :=
pfun.ext $ λ a b, iff_of_eq (congr_fun h_graph (a,b))

/- Partial order structure on the Cohen poset -/
instance partial_order_cohen_poset : partial_order cohen_poset :=
{ le := λ f g, g.val.graph ⊆ f.val.graph,
  lt := λ f g, g.val.graph ⊆ f.val.graph ∧ ¬ f.val.graph ⊆ g.val.graph,
  le_refl := λ _, by unfold has_le.le,
  le_trans := by {intros, apply set.subset.trans, exact a_2, assumption},
  lt_iff_le_not_le := λ _ _, iff.refl _,
  le_antisymm := λ a b h1 h2, by {have := @set.subset.antisymm _ _ _ h2 h1, cases a, cases b,
                                       congr, apply ext_graph, exact this}}

def incompatible {α : Type*} [partial_order α] (a b : α) := ¬ ∃ c, c ≤ a ∧ c ≤ b

def antichain {α : Type*} [partial_order α] (s : set α) := ∀ x ∈ s, ∀ y ∈ s, incompatible x y

def countable_chain_condition (α : Type*) [partial_order α] := ∀ s : set α, antichain s → set.countable s

@[simp]lemma univ_singletons {α : Type*} :  set.Union (λ a, {a}) = (set.univ : set α) :=
by tidy

lemma set_is_union_of_fibers {α β : Type*} (f : α → β) (s : set α) : s = set.Union (λ b, f ⁻¹'{b} ∩ s) := by ext; simp

lemma univ_is_union_of_fibers {α β : Type*} (f : α → β) : @set.univ α = set.Union (λ b, f⁻¹' {b}) :=
begin [smt] eblast_using [set.preimage_Union, @set.preimage_univ α β f, univ_singletons] end

lemma countable_of_bijection_with_countable {α β : Type*} {s : set α} {s' : set β} {f : s → s'}
{hf : function.bijective f} {h' : set.countable s'} : set.countable s :=
begin
  haveI : encodable s' := by apply set.countable.to_encodable h',
  suffices : encodable s, by exact ⟨this⟩, suffices : equiv s s',
  by {apply @encodable.of_equiv s s' (by apply_instance), exact this},
  apply equiv.of_bijective hf
end

lemma countable_of_equiv_with_countable {α β : Type*} {s : set α} {s' : set β}
{h : equiv s s'} {h' : set.countable s'} : set.countable s :=
by {apply countable_of_bijection_with_countable, apply h.bijective, exact h'}

lemma equiv_set_set_univ {α : Type*} (s : set α) : equiv s (@set.univ s) :=
by {unfold set.univ, refine ⟨λ x, ⟨x, (by trivial)⟩, λ x, x.val, _, _⟩, tidy}

/- an (s : set α) is countable if (set.univ : set s) is countable -/
lemma countable_of_countable_univ {α : Type*} (s : set α) : set.countable s ↔ set.countable (set.univ : set s) := 
begin
  split; apply countable_of_equiv_with_countable, symmetry,
  all_goals{apply equiv_set_set_univ}
end

lemma countable_of_countable_fibers {α β : Type*} (s : set α) (f : s → β) [encodable β] (H : ∀ b : β, set.countable (f ⁻¹' {b})) : set.countable s :=
by simp[countable_of_countable_univ, univ_is_union_of_fibers f, set.countable_Union H]

lemma countable_of_countable_fibers' {α β : Type*} (s : set α) (f : α → β) [encodable β] (H : ∀ b : β, set.countable ((f ⁻¹' {b}) ∩ s)) : set.countable s :=
by {rw[set_is_union_of_fibers f s], exact set.countable_Union H}

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

--tidy, {haveI : decidable x := by apply classical.prop_decidable, }, {sorry}

noncomputable instance Prop_encodable : encodable Prop :=
 @encodable.of_equiv _ _ (by apply_instance : encodable bool) equiv_Prop_bool

def size_of_domain : cohen_poset → ℕ := sorry

def is_defined_at (m : ℕ) : set cohen_poset :=
  {p : cohen_poset | ∃ b, (b,m) ∈ (pfun.dom p.val)}

lemma nonempty_domain_defined (p : cohen_poset) (h : 0 < size_of_domain p) : ∃ m,
  is_defined_at m p := sorry

def is_defined_at_covers {n} {h : 0 < n} : size_of_domain ⁻¹' {n} ⊆ ⋃ m, is_defined_at m := sorry

lemma size_of_domain_elim0 : ∀ p, (size_of_domain p = 0 → false) := sorry

lemma size_of_domain_fiber_0 : size_of_domain ⁻¹' {0} = ∅ :=
by ext; simp[size_of_domain_elim0]

lemma cover_Union_eq {α ι : Type*} {s : set α} {t : ι → set α} {h : s ⊆ ⋃ i, t i} :
s = ⋃ i, s ∩ t i :=
by {rw[<-set.inter_Union_left], ext, split; intros, exact ⟨a, h a⟩, exact a.left}

-- TODO both of these should just be instances of the meet-lattice structure on set α
lemma inter_subset_left' {α : Type*} {s t u : set α} {h : t ⊆ u} : s ∩ t ⊆ u :=
  by tidy

lemma inter_subset_right' {α : Type*} {s t u : set α} {h : t ⊆ u} : t ∩ s ⊆ u :=
  by tidy

lemma cohen_poset_ccc : countable_chain_condition cohen_poset :=
begin
  intros a Ha, apply countable_of_countable_fibers' a size_of_domain,
  intro n, induction n,
    {simp[size_of_domain_fiber_0]},
    {let A, swap, change set.countable A,
      have : A ⊆ ⋃ m, is_defined_at m, by {dsimp[A], apply inter_subset_right',
             apply is_defined_at_covers, apply nat.zero_lt_succ},
     rw[@cover_Union_eq _ _ A is_defined_at this], apply set.countable_Union,
     intro m, sorry}
end
