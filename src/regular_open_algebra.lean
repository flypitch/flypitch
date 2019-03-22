import topology.basic tactic.tidy to_mathlib
order.complete_boolean_algebra data.set.basic

local attribute [instance] classical.prop_decidable

open topological_space set

@[instance, priority 1000]def Prop_space : topological_space Prop := ⊤

instance discrete_Prop : discrete_topology Prop := ⟨rfl⟩

instance product_topology {α : Type*} : topological_space (set α) :=
Pi.topological_space

section lemmas
lemma subtype.eq_iff {α : Type*} {P : α → Prop} {a b : subtype P} :
  a = b ↔ a.val = b.val := by tidy

lemma subset_ext {α : Type*} {S₁ S₂ : set α} (H : S₁ ⊆ S₂) (H' : S₂ ⊆ S₁) : S₁ = S₂ := by tidy

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

theorem subset_trans {α : Type*} {a b c : set α} : a ⊆ b →  b ⊆ c → a ⊆ c :=
assume x h, by {intros x Ha, solve_by_elim}

end lemmas

instance Prop_separable : separable_space Prop :=
{ exists_countable_closure_eq_univ :=
  by {use set.univ, refine ⟨countable_encodable _, by simp⟩}}

namespace topological_space
section topology_lemmas
variables {α : Type*} [τ : topological_space α]
local notation `cl`:65 := closure

local notation `int`:65 := interior

attribute [simp] interior_eq_of_open

include τ

def dense {S : set α} : Prop := ∀ U : set α, @is_open α τ U → U ≠ ∅ → U ∩ S ≠ ∅

def nowhere_dense (S : set α) : Prop := int (cl S) = ∅

lemma frontier_closed_of_open {S : set α} (H : @is_open _ τ S) : is_closed (frontier S) :=
begin
  unfold frontier, rw[diff_eq], apply is_closed_inter, tidy
end

lemma frontier_nowhere_dense_of_open {S : set α} (H : @is_open _ τ S) : nowhere_dense (frontier S) :=
begin
  unfold nowhere_dense frontier,
  ext, split; intros, swap, cases a,
  rw[diff_eq] at a,
  rw[show cl(cl S ∩ -int S) = cl(S) ∩ -int S,
    by {apply closure_eq_of_is_closed, from frontier_closed_of_open H}] at a,
  rw[show int S = S, by {apply interior_eq_of_open, from ‹_›}] at a,
  rw[interior_inter] at a, simp at a, tidy
end

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
end topological_space

open topological_space

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

@[simp, ematch]lemma is_open_of_is_regular {S : set α} (H : (: is_regular S :)) : is_open S :=
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

lemma int_cl_eq_p_p {S : set α} : int (cl S) = Sᵖᵖ := p_p_eq_int_cl.symm

@[ematch]lemma mem_int_cl_iff_mem_eq_p_p {S : set α} {a : α} : a ∈ int (cl S) ↔ a ∈ (Sᵖᵖ) := by rw[int_cl_eq_p_p]

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

@[simp]lemma is_regular_eq_p_p {S : set α} (H : is_regular S) : Sᵖᵖ = S :=
begin
  apply subset_ext,
    apply is_regular_stable_subset ‹_›, intros _ _, from ‹_›,
  from in_p_p_of_open (is_open_of_is_regular ‹_›)
end

lemma subset_p_p_of_open {S : set α} (H : (: is_open S :)) : S ⊆ Sᵖᵖ :=
in_p_p_of_open ‹_›

lemma subset_int_cl_of_open {S : set α} (H : is_open S) : S ⊆ int (cl S) :=
by {rw[<-p_p_eq_int_cl], from subset_p_p_of_open ‹_›}

lemma is_regular_sup {S₁ S₂ : set α} : is_regular ((S₁ ∪ S₂)ᵖᵖ) :=
by rw[regular_iff_p_p]; simp

@[simp]lemma is_open_of_p_p' {S : set α} : is_open (Sᵖᵖ) :=
by {simp}

@[simp]lemma is_regular_p_p {S : set α} : is_regular (Sᵖᵖ) :=
begin
  apply subset_ext,
    rw[<-p_p_eq_int_cl], apply subset_p_p_of_open,
    apply is_open_of_p_p',
    rw[<-p_p_eq_int_cl], simp, intros _ _, from ‹_›
end

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

def regular_open.neg : {S : set α // is_regular S} → {S : set α // is_regular S} := λ x, ⟨xᵖ, by {rw[regular_iff_p_p], symmetry, apply p_eq_p_p_p,
                       from is_open_of_is_regular x.property}⟩

@[instance, priority 10000]def regular_open_has_neg : has_neg {S : set α // is_regular S} :=
⟨regular_open.neg⟩


def regular_open.Sup : set {S : set α // is_regular S} → {S : set α // is_regular S} :=
λ 𝒮,⟨⋃₀(subtype.val '' 𝒮)ᵖᵖ, is_regular_p_p⟩

@[instance, priority 10000]def regular_open_has_Sup : has_Sup {S : set α // is_regular S} :=
⟨regular_open.Sup⟩

lemma Sup_unfold {𝒜 : set {S : set α // is_regular S}} : Sup 𝒜 = regular_open.Sup 𝒜 := rfl

lemma regular_open_le_Sup :
  ∀ (s : set {S : set α // is_regular S}) (a : {S // is_regular S}), a ∈ s → a ≤ has_Sup.Sup s :=
begin
  intros s a Ha, intros x Hx, unfold has_Sup.Sup regular_open.Sup,
  simp, suffices : x ∈ (⋃ (x : {S // is_regular S}) (H : x ∈ s), x.val),
  apply subset_int_cl_of_open, {apply is_open_Union, intros, apply is_open_Union,
  intros, from is_open_of_is_regular i.property},
  simp, use a, tidy, recover
end

lemma regular_open_Sup_le :
∀ (s : set {S : set α // is_regular S}) (a : {S // is_regular S}),
    (∀ (b : {S // is_regular S}), b ∈ s → b ≤ a) → has_Sup.Sup s ≤ a :=
begin
  intros 𝒜 A H,
    unfold has_Sup.Sup regular_open_has_Sup regular_open.Sup, simp,
    suffices : (⋃ (x : {S // is_regular S}) (H : x ∈ 𝒜), x.val)ᵖᵖ ⊆ A.val,
      by tidy,
    apply is_regular_stable_subset, from A.property,
    intros a Ha, simp at Ha, tidy
end

lemma perp_self_empty {S : set α} : S ∩ (Sᵖ) = ∅ :=
by tidy

@[simp, priority 0]lemma inf_unfold {x₁ x₂ : {S : set α // is_regular S}} : (x₁ ⊓ x₂) = ⟨x₁.val ∩ x₂.val, is_regular_inter x₁.property x₂.property⟩ :=
by refl

@[simp, priority 0]lemma neg_unfold {x : {S : set α // is_regular S}} : (- x) = ⟨xᵖ, by {rw[regular_iff_p_p], symmetry, apply p_eq_p_p_p,
                       from is_open_of_is_regular x.property}⟩ := by refl
@[simp]lemma neg_neg_eq_self {x : {S : set α // is_regular S}} : - - x = x :=
begin
  simp, apply subtype.eq, simp, apply is_regular_eq_p_p, from x.property
end

@[simp, priority 0]lemma sup_unfold {x₁ x₂ : {S : set α // is_regular S}} :
  (x₁ ⊔ x₂) = ⟨(x₁.val ∪ x₂.val)ᵖᵖ, by {apply is_regular_sup}⟩ := by refl

@[simp, priority 0]lemma top_unfold : (⊤ : {S : set α // is_regular S}).val = set.univ := rfl

lemma regular_open_inf_neg_eq_bot : ∀ (x : {S : set α // is_regular S}), x ⊓ -x = ⊥ :=
by {tidy, suffices : x_val ∩ (x_valᵖ) = (⊥ : {S : set α // is_regular S}).val, apply subtype.eq,
   from this, from perp_self_empty}

lemma regular_open_sup_neg_eq_top : ∀ (x : {S : set α // is_regular S}), x ⊔ -x = ⊤ :=
begin
  intro x, apply subtype.eq, simp, ext, split; intros, trivial,
    tidy, unfold is_regular at x_property, rw[<-x_property] at a_1,
    suffices : cl x_val ∪ - x_val = univ,
      {rw[this] at a_1, apply a_1, simp},
    tidy, by_cases x ∈ x_val,
      left, from subset_closure h,
      right, from ‹_›
end

instance regular_open_boolean_algebra : boolean_algebra {S : set α // is_regular S} :=
{le_sup_inf :=
    begin
      intros x y z, intros a Ha, simp, 
    end,
  sub := λ A B, A ⊓ (-B),
  inf_neg_eq_bot := regular_open_inf_neg_eq_bot,
  sup_neg_eq_top := regular_open_sup_neg_eq_top,
  sub_eq := by {intros x y, refl},
  .. regular_open_has_neg,
  .. regular_open_bounded_lattice
}

@[instance, priority 1000]def regular_open_has_Inf : has_Inf {S : set α // is_regular S} :=
{ Inf := λ 𝒮, ⟨regular_open.neg ((Sup) ((λ x : {S : set α // is_regular S}, -x) '' 𝒮)),
begin
  rw[regular_iff_p_p], change (_)ᵖᵖᵖ = (_)ᵖ, symmetry,
      apply p_eq_p_p_p, rw[Sup_unfold], simp[regular_open.Sup]
end⟩ }

include α
@[simp]lemma Inf_unfold : ∀ s : set {S : set α // is_regular S}, Inf s = - Sup ((λ x, - x) '' s) :=
by tidy

lemma regular_open_Inf_le : ∀s : set {S : set α // is_regular S}, ∀a ∈ s, Inf s ≤ a :=
begin
  intros 𝒜 A H_mem,
  rw[show A = - - A, from (lattice.neg_neg).symm],
  have := lattice.neg_le_neg _,
  convert this, apply regular_open_le_Sup, use A, tidy
end

lemma regular_open_le_Inf : ∀(s : set {S : set α // is_regular S}) a, (∀b∈s, a ≤ b) → a ≤ Inf s :=
begin
  intros 𝒜 A H_mme, rw[show A = - - A, from (lattice.neg_neg).symm],
  rw[Inf_unfold], apply lattice.neg_le_neg _,
  have := regular_open_Sup_le _ _ _,
  convert this, intros, specialize H_mme (-b),
  simp[-neg_unfold] at a,
  rcases a with ⟨w,⟨h₁,⟨h₂,h₃⟩⟩⟩,
    suffices : A ≤ -b,
      replace this := lattice.neg_le_neg this,
      convert this, symmetry, apply neg_neg_eq_self,
      replace h₃ := (congr_arg (λ x, - x) h₃).symm,
      dsimp at h₃, simp only [h₃] at *,
      apply H_mme, simp*
end

instance regular_open_algebra (H_nonempty : nonempty α) :
  nontrivial_complete_boolean_algebra {S : set α // is_regular S} :=
{Inf := λ 𝒮,
    begin
      refine ⟨_,_⟩,
        from regular_open.neg (regular_open.Sup $ (λ x, regular_open.neg x) '' 𝒮),
      rw[regular_iff_p_p], change (_)ᵖᵖᵖ = (_)ᵖ, symmetry,
      apply p_eq_p_p_p, simp[regular_open.Sup]
    end,
  le_Sup := regular_open_le_Sup,
  Sup_le := regular_open_Sup_le,
  Inf_le := regular_open_Inf_le,
  le_Inf := regular_open_le_Inf,
  infi_sup_le_sup_Inf :=
    begin
      sorry
    end,
  inf_Sup_le_supr_inf :=
    begin
      sorry
    end,
  bot_lt_top :=
    by {apply lt_iff_le_and_ne.mpr, split,
       have := regular_open_bounded_lattice.bot_le, specialize this ⊤,
       from this, intro H, simp[subtype.eq_iff] at H,
       change (∅ : set α) = univ at H, tactic.unfreeze_local_instances,
       cases H_nonempty, suffices : H_nonempty ∈ (∅ : set α), by {cases this}, simp[H]},
  .. regular_open_boolean_algebra,
  .. regular_open_has_Sup,
  .. regular_open_has_neg,
  .. regular_open_bounded_lattice
  }


end regular
