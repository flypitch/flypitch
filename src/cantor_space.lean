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
    {ext1, ext1, dsimp at *, fsplit,
      work_on_goal 0 { intros a_1, cases a_1, work_on_goal 0 { cc },
      dsimp at *, solve_by_elim }, intros a_1, rwa[fiber_over_true]},
end

lemma opens_over_le_τ (a : α) : generate_from (opens_over a) ≤ τ a :=
by rw[generate_from_le_iff_subset_is_open]; from opens_over_sub_τ a

lemma τ_le_product_topology (a : α) : τ a ≤ product_topology :=
by {unfold product_topology Pi.topological_space; from le_supr _ _}

lemma le_iff_opens_sub {β : Type*} {τ₁ τ₂ : topological_space β} :
  τ₁ ≤ τ₂ ↔ {S | τ₁.is_open S} ⊆ {S | τ₂.is_open S} := by refl

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

end cantor_space
end cantor_space
