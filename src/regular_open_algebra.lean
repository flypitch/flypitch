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

section lemmas
lemma subtype.eq_iff {α : Type*} {P : α → Prop} {a b : subtype P} :
  a = b ↔ a.val = b.val := by tidy

lemma subset_ext {α : Type*} {S₁ S₂ : set α} (H : S₁ ⊆ S₂) (H' : S₂ ⊆ S₁) : S₁ = S₂ := by tidy

end lemmas

section topology_lemmas
variables {α : Type*} [τ : topological_space α]

include τ
attribute [simp] interior_eq_of_open


theorem subset_trans {a b c : set α} : a ⊆ b →  b ⊆ c → a ⊆ c :=
assume x h, by {intros x Ha, solve_by_elim}

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

lemma compl_mono {s t : set α} (H : s ⊆ t) : - t ⊆ - s := by simp[*,subset_anti]

end topology_lemmas

open lattice
section regular
variables {α : Type*} [τ : topological_space α]

include τ
@[ematch, reducible]def is_regular (S : set α) : Prop := 
 S = interior (closure S)

-- @[reducible,simp,ematch]def int_of_cl (S : set α) := interior (closure S)

@[reducible]def perp (S : set α) := - (closure S)

local postfix `ᵖ`:80 := perp

local notation `cl`:65 := closure

local notation `int`:65 := interior

@[reducible, ematch]lemma perp_unfold (S : set α) : Sᵖ = - (cl S) := rfl

@[simp]lemma is_open_perp {S : set α} : is_open (Sᵖ) :=
by {unfold perp, apply is_open_compl_iff.mpr, simp}

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

lemma is_open_of_p_p {S : set α} (H : Sᵖᵖ = S) : is_open S :=
by {rw[p_p_eq_int_cl] at H, from is_open_of_is_regular (by {unfold is_regular, from H.symm})}

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

@[simp]lemma p_p_p_p_eq_p_p {S : set α} : Sᵖᵖᵖᵖ = Sᵖᵖ :=
by {rw[<-p_eq_p_p_p], simp}

lemma is_regular_stable_subset {S₁ S₂ : set α} (H : is_regular S₂) (H₂ : S₁ ⊆ S₂) : S₁ᵖᵖ ⊆ S₂ :=
by {rw[regular_iff_p_p] at H,
   replace H₂ := p_anti (p_anti H₂), convert H₂, cc}

lemma subset_p_p_of_open {S : set α} (H : is_open S) : S ⊆ Sᵖᵖ :=
in_p_p_of_open ‹_›

lemma is_regular_sup {S₁ S₂ : set α} : is_regular ((S₁ ∪ S₂)ᵖᵖ) :=
by rw[regular_iff_p_p]; simp

@[simp]lemma is_open_of_p_p' {S : set α} : is_open (Sᵖᵖ) :=
by {apply is_open_of_p_p, rw[<-p_eq_p_p_p], simp}

lemma inter_eq_inter_aux (S₁ S₂ : set α) (H : is_open S₁) : S₁ ∩ (cl S₂) ⊆ cl (S₁ ∩ S₂) :=
closure_inter_open ‹_›

@[simp]lemma cl_compl_of_is_open (S : set α) (H : is_open S) : cl(-S) = -S :=
by have : is_closed (-S); by simp*; simp[this]

lemma inter_eq_inter_aux₂ (S₁ S₂ : set α) {H₁ : is_open S₁} {H₂ : is_open S₂} : S₁ ∩ (S₂ᵖᵖ) ⊆ (S₁ ∩ S₂)ᵖᵖ :=
begin
    have this₃ := inter_eq_inter_aux S₁ S₂ H₁,
    have this₄ := compl_mono (this₃),
    rw[compl_inter] at this₄,
    have this₅ := p_anti this₄,
    unfold perp at this₅, rw[closure_union] at this₅,
    rw[cl_compl_of_is_open] at this₅, rw[compl_union] at this₅,
    convert this₅, simp, from ‹_›
end

lemma p_p_inter_eq_inter_p_p {S₁ S₂ : set α} (H₁ : is_open S₁) (H₂ : is_open S₂): (S₁ ∩ S₂)ᵖᵖ = S₁ᵖᵖ ∩ S₂ᵖᵖ :=
begin
  have this₀_left : S₁ ∩ S₂ ⊆ S₁, by simp,
  have this₀_right : S₁ ∩ S₂ ⊆ S₂, by simp,
  have this₁_left : (S₁ ∩ S₂)ᵖᵖ ⊆ S₁ᵖᵖ, from p_anti (p_anti this₀_left),
  have this₁_right : (S₁ ∩ S₂)ᵖᵖ ⊆ S₂ᵖᵖ, from p_anti (p_anti this₀_right),
  have this₂ : (S₁ ∩ S₂)ᵖᵖ ⊆ S₁ᵖᵖ ∩ S₂ᵖᵖ,
    by {intros x Hx, split, from this₁_left ‹_›, from this₁_right ‹_›},
  ext, split, from λ _, this₂ ‹_›,
  suffices : S₁ᵖᵖ ∩ S₂ᵖᵖ ⊆ (S₁ ∩ S₂)ᵖᵖ, from λ _, this ‹_›,
  have this₃ := inter_eq_inter_aux S₁ S₂ H₁,
  have this₄ := compl_mono (this₃),
  have this₅ := p_anti this₄,
  change _ ᵖ ⊆ _ ᵖᵖ at this₅,
  have this₆ : S₁ ∩ (S₂ᵖᵖ) ⊆ (S₁ ∩ S₂)ᵖᵖ,
    by {apply inter_eq_inter_aux₂; from ‹_›},
  have this₇ : (S₁ᵖᵖ) ∩ (S₂ᵖᵖ) ⊆ ((S₁ᵖᵖ) ∩ S₂)ᵖᵖ,
    by {apply inter_eq_inter_aux₂ (S₁ᵖᵖ), simpa},
  have this₈ : (S₂ ∩ S₁ᵖᵖ) ⊆ (S₂ ∩ S₁)ᵖᵖ,
    by {apply inter_eq_inter_aux₂ S₂ S₁; from ‹_›},
  have this₉ : (S₁ᵖᵖ ∩ S₂)ᵖᵖ ⊆ (S₁ ∩ S₂)ᵖᵖᵖᵖ,
    by {replace this₈ := p_anti this₈, replace this₈ := p_anti this₈,
        conv {congr, rw[inter_comm], skip, rw[inter_comm]}, from this₈},
  rw[<-p_eq_p_p_p] at this₉,
  from subset_trans this₇ this₉, from is_open_perp
end

@[simp]lemma is_regular_inter {S₁ S₂ : set α} (H₁ : is_regular S₁) (H₂ : is_regular S₂) : is_regular (S₁ ∩ S₂) :=
by {rw[regular_iff_p_p] at *, rw[p_p_inter_eq_inter_p_p (is_open_of_p_p H₁) (is_open_of_p_p H₂)], cc}

def lattice_opens : complete_lattice (opens α) := by apply_instance

instance regular_open_poset : partial_order {S : set α // is_regular S} :=
{le := λ S₁ S₂, S₁.val ⊆ S₂.val,
  lt := λ S₁ S₂, S₁.val ⊆ S₂.val ∧ S₁.val ≠ S₂.val,
  le_refl := by {intro a, simp only},
  le_trans := by {intros a b c H₁ H₂, apply subset_trans H₁ H₂},
  lt_iff_le_not_le := by {intros a b, split; intro H, tidy,
                      suffices : a_val = b_val,
                      by contradiction, ext; intros; split; intros,
                         from H_left ‹_›, from a ‹_›},
  le_antisymm :=
    begin
      intros a b H₁ H₂, apply subtype.eq,
      ext; intros; split; intros, from H₁ ‹_›, from H₂ ‹_›
    end}

instance regular_open_lattice : lattice {S : set α // is_regular S} :=
{ sup := λ S₁ S₂, ⟨(S₁.val ∪ S₂.val)ᵖᵖ, by {apply is_regular_sup}⟩,
    le_sup_left :=
    begin
      intros a b, refine subset_trans (show a.val ⊆ a.val ∪ b.val, by simp) (show a.val ∪ b.val ⊆ (a.val ∪ b.val)ᵖᵖ, from _),
      apply subset_p_p_of_open (is_open_union (is_open_of_is_regular a.property) (is_open_of_is_regular b.property)),
    end,
  le_sup_right :=
    begin
      intros a b, refine subset_trans (show b.val ⊆ a.val ∪ b.val, by simp) (show a.val ∪ b.val ⊆ (a.val ∪ b.val)ᵖᵖ, from _),
      apply subset_p_p_of_open (is_open_union (is_open_of_is_regular a.property) (is_open_of_is_regular b.property)),
    end,
  sup_le := by {intros a b c H₁ H₂, apply is_regular_stable_subset, from c.property, intros x Hx, cases Hx; solve_by_elim},
  inf := λ S₁ S₂, ⟨S₁.val ∩ S₂.val, by {apply is_regular_inter, from S₁.property, from S₂.property}⟩,
  inf_le_left :=
    begin
      intros a b, intros x Hx, from Hx.left
    end,
  inf_le_right :=
    begin
      intros a b, intros x Hx, from Hx.right
    end,
  le_inf :=
    begin
      intros a b c H₁ H₂, intros x Hx, split; solve_by_elim
    end,
  ..regular_open_poset}

instance regular_open_bounded_lattice : bounded_lattice {S : set α // is_regular S} :=
{  top := ⟨set.univ, is_regular_univ⟩,
  le_top := by tidy,
  bot := ⟨∅, is_regular_empty⟩,
  bot_le := by tidy,
 .. regular_open_lattice}

instance regular_open_has_neg : has_neg {S : set α // is_regular S} :=
⟨λ x, ⟨xᵖ, by {rw[regular_iff_p_p], symmetry, apply p_eq_p_p_p,
                       from is_open_of_is_regular x.property}⟩⟩

instance regular_open_algebra (H_nonempty : nonempty α) : nontrivial_complete_boolean_algebra {S : set α // is_regular S} :=
{le_sup_inf :=
    begin
      intros x y z, intros a Ha, sorry
    end,
  sub := λ A B, A ⊓ (-B),
  inf_neg_eq_bot := sorry,
  sup_neg_eq_top := sorry,
  sub_eq := by {intros x y, refl},
  Sup := sorry,
  Inf := sorry,
  le_Sup := sorry,
  Sup_le := sorry,
  Inf_le := sorry,
  le_Inf := sorry,
  infi_sup_le_sup_Inf := sorry,
  inf_Sup_le_supr_inf := sorry,
  bot_lt_top := by {apply lt_iff_le_and_ne.mpr, split, have := regular_open_bounded_lattice.bot_le, specialize this ⊤, from this, intro H, simp[subtype.eq_iff] at H, change (∅ : set α) = univ at H, tactic.unfreeze_local_instances,
  cases H_nonempty, suffices : H_nonempty ∈ (∅ : set α), by {cases this},
   simp[H]},
  .. regular_open_has_neg,
  .. regular_open_bounded_lattice
  }

end regular
