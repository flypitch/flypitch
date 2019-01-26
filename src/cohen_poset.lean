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

def antichain {α : Type*} [partial_order α] (s : set α) := ∀ x ∈ s, ∀ y ∈ s, (x ≠ y) → incompatible x y

lemma antichain_subset {α : Type*} [partial_order α] {s s' : set α} {h : s' ⊆ s} {hs : antichain s} : antichain s' :=
by {intros _ _ _ _, intro H, apply hs _ _ _ _, tidy}

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

lemma countable_of_injection_to_countable {α β : Type*} {s : set α} {s' : set β} (f : s → s') {hf : function.injective f} (h' : set.countable s') : set.countable s :=
begin
  have := set.countable_iff_exists_injective.mp h', apply set.countable_iff_exists_injective.mpr,
  cases this, refine ⟨this_w ∘ f,_⟩, exact function.injective_comp (this_h) hf
end

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

def size_of_domain : cohen_poset → ℕ := sorry

lemma size_of_domain_fiber {n} {p : cohen_poset} (h : p ∈ size_of_domain ⁻¹' {n}) : size_of_domain p = n := by finish

/-- The partial function p is defined at b and m if (b,m) is in the domain of p -/
def is_defined (p : cohen_poset) (b) (m) := (b,m) ∈ (pfun.dom p.val)

/-- p is defined at m if there exists a b such that p is defined at b and m -/
def is_defined_at (m : ℕ) : set cohen_poset :=
  {p : cohen_poset | ∃ b, is_defined p b m}

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

section one_point_restriction

/- Given x : α, return the set λ a, a ≠ x -/
def not_x {α : Type*} (x : α) : set α := λ a, a ≠ x

def finite_of_inter_not_x {α : Type*} {s : set α} {h : set.finite s} {x : α} : set.finite $ s ∩ not_x x := by {apply set.finite_subset, exact h, apply inter_subset_right', trivial}

def roption_indicator {α : Type*} (s : set α) : α → roption α :=
  λ x, ⟨x ∈ s, λ _, x⟩

def pfun.restriction {α β : Type*} (f : α →. β) (s : set α) : α →. β
:= λ x, do y <- roption_indicator s x, f y

lemma pfun.domain_restriction {α β : Type*} {f : α →. β} {s : set α} : (pfun.restriction f s).dom = f.dom ∩ s :=
  by {/- `tidy` says -/ ext1, dsimp at *, fsplit, work_on_goal 0 { intros a, cases a, fsplit, work_on_goal 0 { assumption }, assumption }, intros a, cases a, fsplit, work_on_goal 0 { assumption }, assumption} -- god bless you tidy

def one_point_restriction (p : cohen_poset) : ∀(x), x ∈ p.val.dom → cohen_poset :=
λ x H, ⟨pfun.restriction p.val (not_x x),
         by {change set.finite (pfun.restriction p.val (not_x x)).dom,
         rw[pfun.domain_restriction], apply finite_of_inter_not_x, apply p.property}⟩

lemma one_point_restriction_decrease_size {n} (p : cohen_poset) (h : size_of_domain p = n + 1) (x) (h_x : x ∈ p.val.dom)  :
size_of_domain (one_point_restriction p x h_x) = n := sorry

end one_point_restriction

lemma cohen_poset_ccc : countable_chain_condition cohen_poset :=
begin
  intros a Ha, apply countable_of_countable_fibers' a size_of_domain,
  intro n, induction n with n ih generalizing a,
    {simp[size_of_domain_fiber_0]},
    {let A_n, swap, change set.countable A_n,
      have : A_n ⊆ ⋃ m, is_defined_at m, by {dsimp[A_n], apply inter_subset_right',
             apply is_defined_at_covers, apply nat.zero_lt_succ},
     rw[@cover_Union_eq _ _ A_n is_defined_at this], apply set.countable_Union,
     intro m, let A_n_m, swap, change set.countable A_n_m,
       have choice_aux : ∀ p : A_n_m, ∃ b : (set $ set ℕ), (b,m) ∈ (pfun.dom p.val.val),
         sorry,
       have := classical.axiom_of_choice choice_aux, cases this with wit wit_spec,
       let eval : A_n_m → Prop :=
             λ (p : ↥A_n_m), pfun.fn ((p.val).val) (wit p, m) (by apply wit_spec),
       apply countable_of_countable_fibers'' _ eval, intro q,
       let A_n_m_q, swap, change set.countable A_n_m_q,
       let A_n' := size_of_domain ⁻¹' {n},
       -- let red : A_n_m_q → A_n' :=
       --   λ X, 
       --     begin rcases X with ⟨⟨p,H_p⟩,H'_p⟩, refine ⟨_,_⟩,
       --       refine one_point_restriction p (wit ⟨p, H_p⟩, m) _, {apply wit_spec},
       --       simp only [set.mem_singleton_iff, set.mem_preimage_eq],
       --       apply one_point_restriction_decrease_size, apply size_of_domain_fiber H_p.left.left
       --   end,

         have := ih (subtype.val '' A_n_m_q) (by {fapply antichain_subset, exact a, /- `tidy` says -/ work_on_goal 0 { intros a_1 a_2, cases a_2, cases a_1, cases a_2_h, cases a_2_w, cases a_2_h_left, cases a_2_w_property, cases a_2_w_val, work_on_goal 0 { induction a_2_h_left, cases a_2_w_property_right, cases a_2_w_property_left, cases a_2_w_property_left_left, work_on_goal 0 {induction a_2_h_right, assumption },induction a_2_h_right, assumption }, cases a_2_w_property, cases a_2_w_val, cases a_2_w_property_right, cases a_2_w_property_left, cases a_2_w_property_left_left, work_on_goal 0 {induction a_2_h_right, assumption }, induction a_2_h_right, assumption }, assumption}), -- sorry floris

         let red : A_n_m_q → size_of_domain ⁻¹' {n} ∩ subtype.val '' A_n_m_q,
           by sorry,
         
         have h_inj : function.injective red,
           by sorry,

          apply countable_of_injection_to_countable red this, exact h_inj}
end
