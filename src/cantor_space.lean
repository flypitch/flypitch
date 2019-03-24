import .to_mathlib .regular_open_algebra tactic.tidy

local attribute [instance] classical.prop_decidable

/- Some facts about Cantor spaces: topological spaces of the form (set α) -/

open topological_space lattice

@[instance, priority 1000]def Prop_space : topological_space Prop := ⊤

instance discrete_Prop : discrete_topology Prop := ⟨rfl⟩

instance product_topology {α : Type*} : topological_space (set α) :=
Pi.topological_space

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

instance Prop_separable : separable_space Prop :=
{ exists_countable_closure_eq_univ :=
  by {use set.univ, refine ⟨set.countable_encodable _, by simp⟩}}

@[ematch]lemma is_open_of_compl_closed {α : Type*} [topological_space α] {S : set α} (H : (: is_closed (-S) :)) : is_open S :=
by rwa[<-is_closed_compl_iff]

@[ematch]lemma is_closed_of_compl_open {α : Type*} [topological_space α] {S : set α} (H : (: is_open (-S) :)) : is_closed S :=
by rwa[<-is_open_compl_iff]

def clopens (α : Type*) [topological_space α] : Type* := {S : set α // is_clopen S}

instance clopens_lattice {α : Type*} [topological_space α] : lattice (clopens α) :=
{ sup := λ S₁ S₂, ⟨S₁.1 ∪ S₂.1, by {apply is_clopen_union, tidy}⟩,
  le := λ S₁ S₂, S₁.1 ⊆ S₂.1,
  lt := λ S₁ S₂, S₁.1 ⊆ S₂.1 ∧ S₁.1 ≠ S₂.1,
  le_refl := by tidy,
  le_trans := by tidy,
  lt_iff_le_not_le :=
    by {intros; split; intros,
      {split, {from a_1.left},
        intro H, apply a_1.right, apply subset_ext, from a_1.left, from ‹_›},
        {/- `tidy` says -/ cases a_1, cases b, cases a, cases a_property,
        cases b_property, dsimp at *, fsplit,
        work_on_goal 0 { assumption }, intros a, induction a, solve_by_elim}},
  le_antisymm := by {intros, apply subtype.eq, apply subset_ext; from ‹_›},
  le_sup_left := by {intros, simp, intros x Hx, left, from ‹_›},
  le_sup_right := by {intros, simp, intros x Hx, right, from ‹_›},
  sup_le := by {intros, intros x Hx, cases Hx, from a_1 ‹_›, from a_2 ‹_›},
  inf := λ S₁ S₂, ⟨S₁.1 ∩ S₂.1, by {apply is_clopen_inter, from S₁.property, from S₂.property}⟩,
  inf_le_left := by {intros, simp, intros x Hx, from Hx.left},
  inf_le_right := by {intros, simp, intros x Hx, from Hx.right},
  le_inf := by {intros, simp, intros x Hx, from ⟨a_1 ‹_›, a_2 ‹_›⟩}}

instance clopens_bounded_lattice {α : Type*} [topological_space α] : bounded_lattice (clopens α) :=
{top := ⟨set.univ, is_clopen_univ⟩,
  le_top := by tidy,
  bot := ⟨∅, is_clopen_empty⟩,
  bot_le := by tidy,
 .. clopens_lattice}

noncomputable def finset_clopens_mk {α : Type*} [topological_space α] {X : finset (set α)} (H : ∀ S ∈ X, is_clopen S) : finset (clopens α) :=
begin
  apply finset.image, show finset _, from finset.attach X,
  intro x, cases x with x Hx, use x, from H x Hx
end

lemma is_clopen_finite_inter {α : Type*} [topological_space α] {X : finset (set α)}
  (H_X : ∀ S ∈ X, is_clopen S) : is_clopen (finset.inf X id) :=
begin
  revert H_X, apply finset.induction_on X, intro _, from is_clopen_univ,
  intros a A H_a H_A IH, simp at ⊢ IH, apply is_clopen_inter,
  from IH a (or.inl rfl), apply H_A, intros S H_S, from IH S (or.inr H_S)
end

lemma is_clopen_finite_inter' {α α' : Type*} [topological_space α] {X : finset α'} {f : α' → set (α)} (H_f : ∀ x ∈ X, is_clopen (f x)) : is_clopen (finset.inf X f) :=
begin
  revert H_f, apply finset.induction_on X, intro _, from is_clopen_univ,
  intros a A H_a H_A IH, simp at ⊢ IH, apply is_clopen_inter,
  from IH a (or.inl rfl), apply H_A, intros S H_S, from IH S (or.inr H_S)
end

namespace cantor_space
section cantor_space
variables {α : Type*}

def principal_open (x : α) : set (set α) := {S | x ∈ S}

def co_principal_open (x : α) : set (set α) := {S | x ∉ S}

@[simp]lemma neg_principal_open {x : α} : co_principal_open x = -(principal_open x)  :=
by unfold principal_open; refl

@[simp]lemma neg_co_principal_open {x : α} : - (co_principal_open x) = principal_open x :=
by {simp[principal_open]}

-- lemma is_open_induced_iff' {α β : Type*} {f : α → β} [t : topological_space β] {s : set α} {f : α → β} :
--    (∃t, is_open t ∧ f ⁻¹' t = s) ↔ @topological_space.is_open α (t.induced f) s := is_open_induced_iff.symm

def opens_over (x : α) : set(set(set α)) := {principal_open x, co_principal_open x, set.univ, ∅}

/-- Given a : α, τ is the topology induced by pulling back the
  discrete topology on Prop along the a'th projection map -/
def τ (a : α) : topological_space (set α) :=
induced (λS, a ∈ S) (by apply_instance : topological_space Prop)

lemma fiber_over_false {α : Type*} {a : α} : (λ x : set α, a ∈ x) ⁻¹' {false} = {y | a ∉ y} :=
begin
  ext, split; simp[set.mem_preimage_eq], tidy {tactics := with_cc}
end

lemma fiber_over_true {α : Type*} {a : α} : (λ x : set α, a ∈ x) ⁻¹' {true} = {y | a ∈ y} :=
begin
  ext, split; simp[set.mem_preimage_eq], tidy {tactics := with_cc}
end

lemma opens_over_sub_τ (a : α) : opens_over a ⊆ (τ a).is_open :=
begin
  unfold τ, intros S HS, unfold opens_over at HS,
  repeat{cases HS}, apply is_open_empty, apply _root_.is_open_univ,
  apply is_open_induced_iff.mpr, fsplit, exact {false}, fsplit,
  apply is_open_discrete,
    {ext1, ext1, dsimp at *, fsplit,
      work_on_goal 0 { intros a_1 a_2, cases a_1,
      work_on_goal 1 { assumption } }, work_on_goal 1 { intros a_1 },
    rwa[<-a_1], rwa[fiber_over_false]},
  apply is_open_induced_iff.mpr, fsplit, exact {true}, fsplit,
  apply is_open_discrete,
    {ext1, ext1, fsplit,
      work_on_goal 0 { intros a_1, cases a_1, work_on_goal 0 { cc },
      dsimp at a_1, cases a_1 }, intros a_1, rwa[fiber_over_true]},
end

lemma opens_over_le_τ (a : α) : generate_from (opens_over a) ≤ τ a :=
by rw[generate_from_le_iff_subset_is_open]; from opens_over_sub_τ a

lemma τ_le_product_topology (a : α) : τ a ≤ product_topology :=
by {unfold product_topology Pi.topological_space; from le_supr _ _}

lemma le_iff_opens_sub {β : Type*} {τ₁ τ₂ : topological_space β} :
  τ₁ ≤ τ₂ ↔ {S | τ₁.is_open S} ⊆ {S | τ₂.is_open S} := by refl

lemma τ_le_opens_over (a : α) : τ a ≤ generate_from (opens_over a) :=
by {apply le_iff_opens_sub.mpr, intros X H, cases H, cases H_h,
   by_cases true ∈ H_w; by_cases false ∈ H_w,
   {constructor, rw[<-H_h_right], unfold opens_over, repeat{split}, right,left,
    ext, by_cases a ∈ x, split, from λ _, trivial, intro, simp[h], from ‹_›,
    split, from λ _, trivial, intro, simp[h], from ‹_›},
   {constructor, rw[<-H_h_right], unfold opens_over, repeat{split}, right, right, right,
     simp, ext, by_cases a ∈ x, split, intro H, simp[principal_open], from ‹_›,
     intro H, simp[*, -H_h_right], split; intros, subst H_h_right, simp* at a_1, cases a_1,
     subst H_h_right, simp[principal_open, *, -a_1] at a_1, cases a_1},
   {constructor, rw[<-H_h_right], unfold opens_over, repeat{split}, right, right, left,
     simp, ext, split; intros; subst H_h_right; simp* at a_1; by_cases a ∈ x,
     tidy {tactics := with_cc}},
   {have : H_w = ∅, ext, split; intros, by_cases x; simp* at a_1; cases a_1, cases a_1,
    subst this, subst H_h_right, simp, by apply @is_open_empty _ (generate_from _)}}

@[simp]lemma is_open_generated_from_basic {β : Type*} [topological_space β] {s : set (set β)} {x ∈ s} :
  is_open (generate_from s) x := by {constructor, from ‹_›}

lemma is_open_principal_open {a : α} : is_open (principal_open a) :=
  by apply (le_trans (opens_over_le_τ a) (τ_le_product_topology _)); simp[opens_over]

lemma is_open_co_principal_open {a : α} : is_open (co_principal_open a) := 
  by apply (le_trans (opens_over_le_τ a) (τ_le_product_topology _)); simp[opens_over]

lemma is_closed_principal_open {a : α} : is_closed (principal_open a) :=
by {apply is_closed_of_compl_open, from is_open_co_principal_open}

lemma is_closed_co_principal_open {a : α} : is_closed (co_principal_open a) :=
by {apply is_closed_of_compl_open,
    simp only [neg_principal_open, lattice.neg_neg], from is_open_principal_open}

lemma is_clopen_principal_open {a : α} : is_clopen (principal_open a) :=
  ⟨is_open_principal_open, is_closed_principal_open⟩

lemma is_clopen_co_principal_open {a : α} : is_clopen (co_principal_open a) :=
  ⟨is_open_co_principal_open, is_closed_co_principal_open⟩

@[reducible]def principal_open_finset (F : finset α) : set (set α) := {S | F.to_set ⊆ S}

@[simp]lemma principal_open_finset_insert {F : finset α} {a : α} : principal_open_finset (insert a F) = principal_open_finset {a} ∩ principal_open_finset F :=
begin
  ext, split; intros; unfold principal_open_finset at *,
  tidy, apply a_1, unfold finset.to_set, simp,
  apply a_1, unfold finset.to_set at *, simp, right, from a_3,
  unfold finset.to_set at *, simp at *, cases a_3,
  apply a_1_left, from a_3, apply a_1_right, from a_3
end

lemma principal_open_finset_eq_inter (F : finset α) : principal_open_finset F = (finset.inf F (principal_open)) :=
begin
  apply finset.induction_on F,
    {tidy},
  intros a A h_a IH, simp, rw[<-IH], ext, split; intros,
  tidy, apply a_1_left, simp[finset.to_set]
end

@[reducible] def co_principal_open_finset (F : finset α) : set (set α) := {S | F.to_set ⊆ (-S)}

@[simp]lemma co_principal_open_finset_insert {F : finset α} {a : α} : co_principal_open_finset (insert a F) = co_principal_open_finset {a} ∩ co_principal_open_finset F :=
begin
  ext, split; intros; unfold co_principal_open_finset at *,
  split, intros a_2 H, simp at a_1, apply a_1, unfold finset.to_set at ⊢ H,
  {tidy}, intros a_2 H, simp at a_1, apply a_1, unfold finset.to_set at ⊢ H,
  {tidy, right, from ‹_›}, intros a_2 H, simp[finset.to_set] at *,
  cases H; [apply a_1.left, apply a_1.right]; simpa
end

lemma co_principal_open_finset_eq_inter (F : finset α) : co_principal_open_finset F = (finset.inf F (co_principal_open)) :=
begin
  apply finset.induction_on F,
    {tidy},
  intros a A h_a IH, simp, rw[<-IH], ext, split; intros,
  tidy, apply a_1_left, simp[finset.to_set], from a_1
end

lemma is_clopen_principal_open_finset (F : finset α) : is_clopen (principal_open_finset F) :=
begin
  rw[principal_open_finset_eq_inter], apply is_clopen_finite_inter',
  from λ _ _, is_clopen_principal_open
end

lemma is_clopen_co_principal_open_finset (F : finset α) : is_clopen (co_principal_open_finset F) :=
begin
  rw[co_principal_open_finset_eq_inter], apply is_clopen_finite_inter',
  from λ _ _, is_clopen_co_principal_open
end

lemma product_topology_generated_from : (product_topology : topological_space (set α)) = generate_from (⋃(a : α), opens_over a) :=
begin
  apply le_antisymm, refine supr_le _, intro a,
  refine le_trans (τ_le_opens_over a) _, apply generate_from_mono,
  intros X H, constructor, simp, use a, from H,

  unfold product_topology Pi.topological_space, change _ ≤ generate_from _,
  apply generate_from_mono,
  intros X HX, rcases HX with ⟨W, ⟨H₁, H₂⟩⟩, simp, cases H₁ with a Ha,
  use τ a, split, use a, refl, apply opens_over_le_τ a, constructor, cc
end


end cantor_space
end cantor_space