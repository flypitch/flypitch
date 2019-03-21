import topology.basic tactic.tidy cohen_poset order.complete_boolean_algebra

local attribute [instance] classical.prop_decidable

open topological_space set

@[instance, priority 1000]def Prop_space : topological_space Prop := ⊤

instance discrete_Prop : discrete_topology Prop := ⟨rfl⟩

instance product_topology {α : Type*} : topological_space (set α) :=
Pi.topological_space

instance Prop_separable : separable_space Prop :=
{ exists_countable_closure_eq_univ :=
  by {use set.univ, refine ⟨countable_encodable _, by simp⟩}}

section topology_lemmas
variables {α : Type*} [τ : topological_space α]

include τ
attribute [simp] interior_eq_of_open

@[ematch]lemma is_clopen_interior {S : set α} (H : (: is_clopen S :)) : interior S = S :=
interior_eq_of_open H.left

@[ematch]lemma is_clopen_closure {S : set α} (H : (: is_clopen S :)) : closure S = S :=
closure_eq_of_is_closed H.right

@[ematch, simp]lemma closure_mono' {s t : set α} (H : (: s ⊆ t :)) : closure s ⊆ closure t ↔ true := by finish[closure_mono]

@[ematch]lemma closure_eq_compl_interior_compl' {s : set α} :
  closure s = - interior (- s) := closure_eq_compl_interior_compl

lemma interior_compl' {s : set α} : interior (- s) = - closure s :=
by apply interior_compl

@[ematch]lemma interior_eq_compl_closure_compl {s : set α} :
  interior s = - closure (- s) :=
by ext; simp

lemma subset_anti {s t : set α} : -s ⊆ -t ↔ t ⊆ s :=
compl_subset_compl

@[ematch]lemma subset_anti' {s t : set α} (H : t ⊆ s) :  - (closure s) ⊆ - (closure t) :=
by finish[subset_anti]

@[ematch]lemma subset_anti_right {s t : set α} (H : s ⊆ -t) : s ⊆ -t ↔ t ⊆ -s :=
by {split, clear H, intro, rw[<-subset_anti], convert a, simp, finish}


end topology_lemmas

open lattice
section regular
variables {α : Type*} [τ : topological_space α]

include τ
@[ematch, reducible]def is_regular (S : set α) : Prop := 
 S = interior (closure S)

-- @[reducible,simp,ematch]def int_of_cl (S : set α) := interior (closure S)

@[reducible, simp]def perp (S : set α) := - (closure S)

local postfix `ᵖ`:80 := perp

local notation `cl`:65 := closure

local notation `int`:65 := interior

@[reducible, ematch]lemma perp_unfold (S : set α) : Sᵖ = - (cl S) := rfl

@[simp]lemma is_open_of_is_regular {S : set α} (H : is_regular S) : is_open S :=
by {unfold is_regular at H, rw[H], simp}

@[simp]lemma is_regular_of_clopen {S : set α} (H : is_clopen S) : is_regular S :=
by {[smt] eblast}

lemma regular_iff_p_p {S : set α} : is_regular S ↔ (Sᵖᵖ) = S :=
begin
  split; intro H, unfold is_regular at H,
  {[smt] eblast},
  {[smt] eblast}
end

lemma p_p_eq_int_cl {S : set α} : Sᵖᵖ = interior (closure S) :=
by {have := @regular_iff_p_p α _ S; {[smt] eblast}}

@[simp]lemma is_regular_empty : is_regular (∅ : set α) :=
by simp

@[simp]lemma is_regular_univ : is_regular (univ : set α) :=
by simp

lemma p_anti {P Q : set α} (H : P ⊆ Q) : Qᵖ ⊆ Pᵖ :=
by {have := subset_anti' H, from this}

lemma in_p_p_of_open {S : set α} (H : is_open S) : S ⊆ Sᵖᵖ :=
begin
  have : S ⊆ cl S := subset_closure,
  rw[<-subset_anti] at this,
  replace this := closure_mono this,
  rw[<-subset_anti] at this,
  convert this, simp*
end

lemma p_eq_p_p_p {S : set α} (H : is_open S) : Sᵖ = Sᵖᵖᵖ :=
begin
  have := p_anti (in_p_p_of_open ‹_›),
  have := in_p_p_of_open (show is_open (Sᵖ), by simp),
  ext; split; intros; solve_by_elim
end

lemma p_p_inter_eq_inter_p_p {S₁ S₂ : set α} : sorry := sorry

@[simp]lemma is_regular_inter {S₁ S₂ : set α} (H₁ : is_regular S₁) (H₂ : is_regular S₂) : is_regular (S₁ ∩ S₂) :=
begin
  sorry 
end

def lattice_opens : complete_lattice (opens α) := by apply_instance

instance regular_open_algebra : complete_boolean_algebra {S : set α // is_regular S} :=
{ sup := λ S₁ S₂, ⟨S₁.val ∪ S₂.val, sorry⟩,
  le := λ S₁ S₂, S₁.val ⊆ S₂.val,
  lt := λ S₁ S₂, S₁.val ⊆ S₂.val ∧ S₁.val ≠ S₂.val,
  le_refl := by {intro a, simp only},
  le_trans := by {sorry},
  lt_iff_le_not_le := sorry,
  le_antisymm := sorry,
  le_sup_left := sorry,
  le_sup_right := sorry,
  sup_le := sorry,
  inf := λ S₁ S₂, ⟨S₁.val ∩ S₂.val, sorry⟩,
  inf_le_left := sorry,
  inf_le_right := sorry,
  le_inf := sorry,
  le_sup_inf := sorry,
  top := ⟨set.univ, is_regular_univ⟩,
  le_top := sorry,
  bot := ⟨∅, is_regular_empty⟩,
  bot_le := sorry,
  neg := sorry,
  sub := sorry,
  inf_neg_eq_bot := sorry,
  sup_neg_eq_top := sorry,
  sub_eq := sorry,
  Sup := sorry,
  Inf := sorry,
  le_Sup := sorry,
  Sup_le := sorry,
  Inf_le := sorry,
  le_Inf := sorry,
  infi_sup_le_sup_Inf := sorry,
  inf_Sup_le_supr_inf := sorry }

end regular
