import .zfc
open fol
open zfc

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

@[simp] lemma realize_term_remove_irrel {n : ℕ} {L : Language} {S : Structure L} {v : dvector ↥S (n+1)} {j : fin n} {k : ℕ} {p : k > j} : realize_bounded_term v ((lift_bounded_term_at (bd_var j : bounded_term L n) 1 k) ) dvector.nil = realize_bounded_term (dvector.remove_mth k v)  (bd_var j) dvector.nil :=
begin
sorry
end

set_option trace.check true
 

@[simp]lemma Set'_realize_subset_2 : ∀ x y : Set, @realize_bounded_formula L_ZFC Set' 2 0 (x :: y :: dvector.nil) subset  dvector.nil  = Set.subset x y:=
begin
  simp only [subset, Set'_mem_mem, fol.realize_bounded_formula, fol.realize_bounded_term, dvector.nth],
  intros, conv {to_lhs, change ∀ z, z ∈ x → z ∈ y}, rw [Set.subset]
end
set_option trace.app_builder true

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
  simp, change ∃ U, ∀ z, z ∈ U ↔ ∃ w, z ∈ w ∧ w ∈ x, 
  refine ⟨⋃ x, _⟩, intro z, rw[@Set.mem_Union x z], finish
end

lemma Set'_models_powerset : axiom_of_powerset ∈ Th Set' := 
begin
  simp only [Th, axiom_of_powerset, small,  fol.realize_bounded_formula_ex,
 fol.realize_bounded_formula, realize_bounded_formula_biimp, set.mem_set_of_eq],
  intros,
  refine ⟨Set.powerset x, _⟩,
  intro y, change y ∈ Set.powerset x ↔ Set.subset y x,
  exact Set.mem_powerset,
end

lemma Set'_models_choice : axiom_of_choice ∈ Th Set' := sorry

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
    {refine ⟨∅, ⟨_, Set.omega_zero⟩⟩, apply Set.mem_empty},
    {intros z H, refine ⟨Set.insert z z, ⟨iff.mpr Set.mem_insert (or.inl (by refl)), @Set.omega_succ z H⟩⟩},
end

lemma shallow_infinity_iff_shallow_infinity' : Set_axiom_of_infinity ↔ Set_axiom_of_infinity' :=
  sorry

lemma Set'_infinity_shallow_infinity : Set'[axiom_of_infinity] ↔ Set_axiom_of_infinity  :=
  sorry

lemma Set'_infinity'_shallow_infinity' :  Set'[axiom_of_infinity'] ↔ Set_axiom_of_infinity' :=
  sorry
 
example : axiom_of_infinity ∈ Th(Set') :=
  Set'_infinity_shallow_infinity.mpr Set'_models_shallow_infinity

example : axiom_of_infinity' ∈ Th(Set') :=
      Set'_infinity'_shallow_infinity'.mpr $ shallow_infinity_iff_shallow_infinity'.mp Set'_models_shallow_infinity

@[simp]lemma Set'_functional_rw : ∀ c : bounded_formula L_ZFC 2, @realize_bounded_formula L_ZFC Set' 0 0 dvector.nil (functional c) dvector.nil = ∀ x : Set, ∃ y : Set, ∀ w, @realize_bounded_formula L_ZFC Set' 3 0  ([w,y,x]) ( (c ↑' 1 # 1) ⇔ &0 ≃ &1)  dvector.nil := 
begin
intros c,
ext1, simp at *, rw [functional, realize_bounded_formula],
simp [realize_bounded_formula_ex],
refl
end

lemma Set'_functional : ∀ c, @realize_bounded_formula L_ZFC Set' 0 0 dvector.nil (functional c) dvector.nil → Set → Set :=
begin
  intro c, rw[Set'_functional_rw], intros h s, sorry
end

lemma Set'_models_replacement: ∀ c : bounded_formula L_ZFC 2, axiom_of_replacement c ∈ Th Set' := 
begin
intro c,
simp only [has_mem.mem,set.mem,Th,set_of,axiom_of_replacement],
intros a x,
sorry
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
