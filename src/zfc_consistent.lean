import .zfc
open fol
open zfc

universe u

local infix `∈'`:100 := bounded_formula_of_relation ZFC_el
local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`:0) := l

def L_ZFC_structure_of_Set : Structure L_ZFC :=
begin
  refine ⟨Set,_,_⟩,
  {intros n f, repeat{cases f}},
  {intros n r v, cases r, cases v, cases v_xs, exact v_x ∈ v_xs_x}
end

local notation `Set'` := L_ZFC_structure_of_Set

instance has_mem_Set'_Set' : (has_mem Set' Set') := ⟨Set.mem⟩

instance has_mem_Set_Set' : has_mem Set.{0} Set' := ⟨Set.mem⟩

instance has_emptyc_Set' : has_emptyc Set' := ⟨Set.empty⟩

lemma  empty_subset : ∀ x: Set',  Set.empty ⊆ x := by tidy 

lemma Set'_Set : ↥Set' = Set := by refl

@[simp]lemma Set'_Set_2 {p : (by exact ↥Set') → Prop} : (λ x, p x) = λ x : Set, p x := by refl

lemma Set'_has_mem : has_mem ↥Set' ↥Set' := ⟨ Set.mem ⟩
local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

example : Set' ⊨ (∃' is_emptyset) :=
begin
  unfold is_emptyset, simp[realize_sentence_ex], refine ⟨∅, _⟩, tidy
end

@[simp]lemma Set'_rel_mem {x y : Set} :  (Structure.rel_map Set' ZFC_rel.ϵ ( [x,y] ) ) = (x ∈ y) := by tidy
 
@[simp] lemma Set'_mem_mem {n : ℕ} {x y : bounded_term L_ZFC n} {v : dvector ↥Set' n} : realize_bounded_formula v (x ∈' y) dvector.nil = ((realize_bounded_term v x dvector.nil) ∈ (realize_bounded_term v y dvector.nil)) := begin
  simp [ZFC_el, bounded_formula_of_relation, realize_bounded_formula, bd_apps_rel] end 

lemma Set_subset_rw {s t : Set} : @realize_bounded_formula L_ZFC Set' 2 0 ([s,t]) subset ([]) ↔ Set_subset s t :=
 by {simp only [subset],
    simp only [realize_bounded_formula, Set'_mem_mem, Set_subset, Set.subset], refl}

lemma Set_is_powerset_rw {s t : Set}: @realize_bounded_formula L_ZFC Set' 2 0 ([t,s]) is_powerset ([]) ↔ Set_is_powerset s t :=
by {simp only [is_powerset, realize_bounded_formula, realize_bounded_formula_biimp, Set'_mem_mem, Set_is_powerset, realize_cast_bounded_formula, dvector.trunc, Set_subset_rw, Set_subset],refl}

lemma Set_is_emptyset_rw {s : Set} : @realize_bounded_formula L_ZFC Set' 1 0 ([s]) is_emptyset ([]) ↔ Set_is_emptyset s :=
by {simp only [is_emptyset, realize_bounded_formula,realize_bounded_formula_not,realize_bounded_formula_ex,Set_is_emptyset], refl}

lemma Set_pair_rw {s t p: Set} : @realize_bounded_formula L_ZFC Set' 3 0  ([p,s,t]) pair ([]) ↔ Set_pair_predicate p s t :=
by {simp only [pair, Set_pair_predicate, realize_bounded_formula_or, realize_bounded_formula], refl}

lemma Set_ordered_pair_rw' {s t p: Set} : @realize_bounded_formula L_ZFC Set' 3 0 ([p,s,t]) ordered_pair ([]) ↔ Set_ordered_pair' p s t :=
by {simp only [ordered_pair, realize_bounded_formula_biimp, realize_bounded_formula_and, realize_bounded_formula, realize_bounded_formula_or, Set'_mem_mem, realize_cast_bounded_formula, Set_ordered_pair, dvector.trunc, Set_pair_rw], 
  refl}
lemma Set_ordered_pair_rw {s t p} : Set_ordered_pair s t p ↔ Set_ordered_pair s t p :=
by {simp only [Set_ordered_pair, Set_ordered_pair'], sorry}
--TODO : angle bracket notation ⟪x,y⟫ = {{x},{x,y}}

lemma Set_is_ordered_pair_rw {p}: @realize_bounded_formula L_ZFC Set' 1 0 ([p]) is_ordered_pair ([]) ↔ Set_is_ordered_pair' p :=
by {simp only [is_ordered_pair, Set_is_ordered_pair', realize_cast_bounded_formula, realize_bounded_formula, realize_bounded_formula_ex, dvector.trunc, Set_ordered_pair_rw'], refl}

lemma Set_relation_rw {p} : @realize_bounded_formula L_ZFC Set' 1 0 ([p]) relation ([]) ↔ Set_relation p :=
by {simp only [relation, Set_relation, realize_bounded_formula, realize_cast_bounded_formula, dvector.trunc, Set_is_ordered_pair_rw, Set'_mem_mem], refl}

lemma Set_function_rw {p} : @realize_bounded_formula L_ZFC Set' 1 0 ([p]) function ([]) ↔ Set_function' p :=
by {simp only [function, Set_function', realize_bounded_formula, realize_bounded_formula_and, realize_cast_bounded_formula, dvector.trunc, Set_ordered_pair_rw', Set'_mem_mem, Set_relation_rw],refl}

@[simp]lemma Set'_realize_subset_2 : ∀ x y : Set, @realize_bounded_formula L_ZFC Set' 2 0 (x :: y :: dvector.nil) subset  dvector.nil  = Set.subset x y:=
begin
  simp only [subset, Set'_mem_mem, fol.realize_bounded_formula, fol.realize_bounded_term, dvector.nth],
  intros, conv {to_lhs, change ∀ z, z ∈ x → z ∈ y}, rw [Set.subset]
end

@[simp]lemma Set'_realize_is_empty : ∀ x, (@realize_bounded_formula L_ZFC Set' _ _ ([x]) is_emptyset dvector.nil ↔ x = ∅) :=
begin
  intro x, unfold is_emptyset,
   simp only [not_exists, fol.realize_bounded_formula_ex, Set'_mem_mem,
   fol.realize_bounded_formula, fol.realize_bounded_formula_not, fol.realize_bounded_term],
   symmetry, apply Set.eq_empty
end
 
@[simp]lemma Set'_realize_empty : @realize_bounded_formula L_ZFC Set' 1 0 (Set.empty :: dvector.nil) is_emptyset dvector.nil :=
by rw[Set'_realize_is_empty]; refl

-- set_option trace.simplify.rewrite true

lemma Set'_models_extensionality : axiom_of_extensionality ∈ Th Set' := 
begin
  simp [Th, axiom_of_extensionality, fin.val, has_one.one, fin.of_nat],
  intros x y, intro h, apply Set.ext, intro z, revert h,  intro h, have := h z, exact this
end

lemma Set'_models_union : axiom_of_union ∈ Th Set' := 
begin
  simp only [Th, axiom_of_union, small], intro x,
  conv {congr, skip, congr, congr, congr, skip,
       change (∃' (&1 ∈' &0 ⊓ &0 ∈' &3) : bounded_formula L_ZFC 3)},
  simp only [realize_bounded_formula, realize_bounded_formula_ex,
      realize_bounded_formula_and, realize_bounded_formula_biimp,
    Set'_mem_mem], 
  change ∃ U, ∀ z, z ∈ U ↔ ∃ w, z ∈ w ∧ w ∈ x, 
  refine ⟨⋃ x, _⟩, intro z, rw[@Set.mem_Union x z], finish
end

lemma Set'_models_powerset : axiom_of_powerset ∈ Th Set' := 
begin
  simp only [Th, axiom_of_powerset, small,  fol.realize_bounded_formula_ex,
 fol.realize_bounded_formula, realize_bounded_formula_biimp, set.mem_set_of_eq],
  intros,
  refine ⟨Set.powerset x, _⟩,
  intro y, change y ∈ Set.powerset x ↔ Set.subset y x,
  exact Set.mem_powerset
end

def Set_pair (x y : Set.{u}) : Set.{u} := {x, y}

noncomputable instance map_definable_aux (f : Set → Set) [H : pSet.definable 1 f] : pSet.definable 1 (λy, Set_pair y (f y)) :=
@classical.all_definable 1 _
noncomputable def Set_map (f : Set → Set) [H : pSet.definable 1 f] : Set → Set :=
Set.image (λy, Set_pair y (f y))

noncomputable def choice_map : Set → Set := λ x, @Set_map (λy, classical.epsilon (λz, z ∈ y)) (classical.all_definable _) x

lemma Set_not_mem_self: ∀ {z : Set}, z ∉ z :=
begin
intro z, apply Set.induction_on z,
intros, have h:= classical.em (x ∈ x),
cases h, {exact a x h},
{exact h}
end

lemma Set'_models_shallow_simple_choice : Set_axiom_of_choice' :=
begin
unfold Set_axiom_of_choice', 
intro x, refine ⟨choice_map x, _⟩,
intros z h, cases h with h nonempty, rw choice_map, rw Set_map, 
refine ⟨classical.strong_indefinite_description (λ e, e ∈ z) _, _ ⟩,
{simp},
repeat {apply and.intro},
{cases classical.strong_indefinite_description _ _, exact property nonempty},
refine ⟨Set_pair z (classical.epsilon (λ (e : Set), e ∈ z)), _⟩,
repeat {apply and.intro}, simp, refine ⟨z, _⟩, apply and.intro, 
{assumption},
{refl}, 
{rw [Set_pair], exact Set.mem_insert.mpr(or.inr (Set.mem_insert.mpr (or.inl rfl)))}, 
{rw [Set_pair],refine Set.mem_insert.mpr(or.inl _),rw [classical.epsilon, nonempty_of_inhabited], refl},
{intros w' h, cases h with mem h, cases h with v h, cases h with a b, cases b with b c,
simp at a, cases a with y h, rw← h.2 at *, rw Set_pair at *, simp at b, simp at c, cases b, cases c,
{rw [b,c] at mem, exact false.elim (Set_not_mem_self mem)},
{rw← b at c, rw classical.epsilon at c, exact c}, cases c,
{rw classical.epsilon at b, cases nonempty_of_inhabited, cases c, cases classical.strong_indefinite_description _ _, rw c at mem, },
{}
}
end

lemma Set'_models_choice : axiom_of_choice ∈ Th Set' := 
begin
simp [has_mem.mem, set.mem, Th, set_of, axiom_of_choice, satisfied_in],
end

lemma Set'_models_infinity : axiom_of_infinity ∈ Th Set' :=
begin
  simp [has_mem.mem, set.mem, Th, set_of, axiom_of_infinity,satisfied_in], 
  refine ⟨Set.omega, _⟩, refine ⟨_,_⟩, refine ⟨Set.empty,_⟩,
  refine ⟨Set'_realize_empty, by {change Set.empty ∈ Set.omega, exact Set.omega_zero}⟩,
  intros, refine ⟨Set.insert x x, _⟩, refine ⟨_,@Set.omega_succ x a⟩,
  exact (iff.mpr Set.mem_insert (or.inl (refl x)))
end

lemma Set'_models_infinity' : axiom_of_infinity' ∈ Th Set' :=
begin
  simp [has_mem.mem, set.mem, Th, set_of, axiom_of_infinity' ,satisfied_in,realize_cast_bounded_formula], 
  refine ⟨Set.omega, _⟩, intro x, refine ⟨_,_⟩,
  {intro H_x, change Set.mem x _, change _ ∈ Set.omega,
  suffices : x = Set.empty, by rw[this]; apply Set.omega_zero, exact H_x},
  intro y, conv in (dvector.nth _ _ _) {change x}, conv in (dvector.nth _ _ _) {change y},
  change Set.mem y Set.omega → _, intro H,
  exact ⟨Set.insert y y, ⟨iff.mpr Set.mem_insert (or.inl (by refl)), @Set.omega_succ y H⟩⟩
end

lemma Set'_models_shallow_infinity : Set_axiom_of_infinity :=
begin
  unfold Set_axiom_of_infinity Set_is_emptyset, refine ⟨Set.omega, _⟩,
  split,
    {refine ⟨∅, ⟨_, Set.omega_zero⟩⟩, intro y, cases y, exact Set.mem_empty y_w y_h},
    {intros z H, refine ⟨Set.insert z z, ⟨iff.mpr Set.mem_insert (or.inl (by refl)), @Set.omega_succ z H⟩⟩},
end

lemma shallow_infinity_iff_shallow_infinity' : Set_axiom_of_infinity ↔ Set_axiom_of_infinity' :=
begin
sorry
end

lemma Set'_infinity_shallow_infinity : Set'[axiom_of_infinity] ↔ Set_axiom_of_infinity  :=
  sorry

lemma Set'_infinity'_shallow_infinity' :  Set'[axiom_of_infinity'] ↔ Set_axiom_of_infinity' :=
  sorry
 
example : axiom_of_infinity ∈ Th(Set') :=
  Set'_infinity_shallow_infinity.mpr Set'_models_shallow_infinity

example : axiom_of_infinity' ∈ Th(Set') :=
      Set'_infinity'_shallow_infinity'.mpr $ shallow_infinity_iff_shallow_infinity'.mp Set'_models_shallow_infinity


/-TODO: generalize arity-/
@[simp]def Set'_realize_formula_relation (c : bounded_formula L_ZFC 2) : Set → Set → Prop := λ s t, @realize_bounded_formula L_ZFC Set' 2 0 (s:: t :: dvector.nil) c dvector.nil   

@[simp] lemma Set'_formula_to_relation (c : bounded_formula L_ZFC 2) : ∀ s t, @realize_bounded_formula L_ZFC Set' 2 0 (s :: t :: dvector.nil) c dvector.nil ↔ Set'_realize_formula_relation c s t := by simp


@[simp]def Set'_functional_prop (r : Set → Set → Prop) (x: Set) : Set → Prop :=  λ y, ∀ z, r x z ↔ y = z


@[simp]def Set'_functional : (Set → Set → Prop) → Prop := λ r, ∀ s, ∃ y, ∀ z, (∀ z₁ s₁, (s₁ = s ∧ z₁ = z) → (r s₁ z₁ ↔ z₁ = y))


noncomputable def Set'_functional_to_function : ∀ r : Set → Set → Prop, Set'_functional r → (Set → Set) := 
begin
rw Set'_functional,
intros r a s, 
refine (classical.indefinite_description _ _).val,
exact  λ y, ∀ z, ∀ z₁, ∀ s₁, ((s₁ = s ∧ z₁ = z ) → (r s₁ z₁ ↔ z₁ = y)),
exact a s,
end
/-
noncomputable lemma Set'_functional_rewrite  (r : Set → Set → Prop) (a : Set'_functional r) : ∀ w z q t,(t = w ∧ q = z → ( r t q ↔ Set'_functional_to_function r a t = q)) :=
begin
rw Set'_functional_to_function,
rw eq.mpr, simp, intros, 
fsplit, intro, cases a_1, cases a_2, dsimp at *, cases classical.indefinite_description _ _, simp, refine (property z z w _).mp a_3,
exact and.intro a_1 a_2,
cases classical.indefinite_description _ _, simp, 
end
-/
noncomputable def Set'_functional_image : ∀ r : Set → Set → Prop, Set'_functional r → (Set → Set) := 
begin
intros,
refine @Set.image _ _ a_1,
exact Set'_functional_to_function r a,
refine classical.all_definable _,
end

@[simp]lemma Set'_functional_mem (r : Set.{0} → Set.{0} → Prop) (a: Set'_functional r) : ∀ (x : Set) (z : Set), Set.mem z (Set'_functional_image r a x) ↔ ∀ x₁ z₁, (z₁ = z ∧ x₁ = x) → ∃ (w : Set), r w z₁ ∧ Set.mem w x₁ :=
begin
rw Set'_functional_image, 
intros x z, 
 dsimp, fsplit, 
{intro h, 
  have y := ((@Set.mem_image (Set'_functional_to_function r a) (classical.all_definable _) x z).mp h),
  cases y, intros, cases a_1.left, cases a_1.right, refine ⟨y_w, _⟩,
  cases y_h, repeat {cases y_h_h}, refine and.intro _ y_h_w,
  cases ((classical.indefinite_description _ _)), 
  simp, refine ((property val val y_w _).mpr (eq.refl val)), finish},
{ intro h, cases h x z (and.intro (eq.refl z)(eq.refl x)), rw Set'_functional_to_function, rw eq.mpr,dsimp, refine (@Set.mem_image _ (classical.all_definable _) _ _).mpr _, refine ⟨w, ⟨h_1.2, _⟩⟩, cases (classical.indefinite_description _ _), dsimp, refine ((property z z w _).mp h_1.1).symm, finish}
end

lemma Set'_shallow_replacement : ∀ r : (Set.{0} → Set.{0} → Prop), Set'_functional r → ∀ x : Set, ∃ y : Set, ∀z, Set.mem z y ↔ (∀ x₁ z₁, (z₁ = z ∧ x₁ = x) →∃ w : Set, (r w z₁) ∧ Set.mem w x₁) := 
begin
  intros,
  refine ⟨Set'_functional_image r a x, _⟩,
  exact Set'_functional_mem r a x,
end


lemma Set'_realize_functional_relation : ∀ (c: bounded_formula L_ZFC 2), @realize_bounded_formula L_ZFC Set' _ _ dvector.nil (functional c) dvector.nil ↔ Set'_functional (Set'_realize_formula_relation c) :=  
begin
intros,
rw functional,
simp only [realize_bounded_formula,realize_bounded_formula_ex, realize_bounded_formula_and,realize_bounded_formula_biimp, Set'_functional, Set'_realize_formula_relation], simp only [realize_cast_bounded_formula], dsimp,  
refl 
end

lemma Set'_models_replacement: ∀ c : bounded_formula L_ZFC 2, axiom_of_replacement c ∈ Th Set' := 
begin
intro c,
simp only [has_mem.mem,set.mem,Th,set_of,axiom_of_replacement],
simp only [realize_sentence, realize_bounded_formula], 
rw Set'_realize_functional_relation,
rw small', 
simp only [realize_bounded_formula, realize_bounded_formula_ex, realize_bounded_formula_and, realize_bounded_formula_biimp, realize_cast_bounded_formula, Set'_mem_mem,dvector.trunc], have h₁ := Set'_shallow_replacement (Set'_realize_formula_relation c),
exact h₁
end

lemma Set_extends_ZFC : ZFC ⊆ Th Set' :=
begin
intros f hf, cases hf with zf choice,
repeat{cases zf},
  exact Set'_models_infinity, exact Set'_models_powerset,
  exact Set'_models_union, exact Set'_models_extensionality,
  dsimp at zf_h, cases zf_h with a b, subst b,
  revert zf_w, simp, exact Set'_models_replacement, 
  repeat{cases choice}, exact Set'_models_choice
end
