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

instance  has_mem_Set'_Set' : (has_mem Set' Set') := ⟨Set.mem⟩

instance has_mem_Set_Set' : has_mem Set.{0} Set' := ⟨Set.mem⟩

instance has_emptyc_Set' : has_emptyc Set' := ⟨Set.empty⟩

lemma  empty_subset : ∀ x: Set',  Set.empty ⊆ x := by tidy 

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
@[simp]lemma realize_bounded_formula_biimp { n : ℕ } {L : Language } { S : Structure L} {f₁ f₂ : bounded_formula L n} {v : dvector ↥S n} : (realize_bounded_formula v (f₁ ⇔ f₂) dvector.nil) = ((realize_bounded_formula v f₁ dvector.nil) ↔ (realize_bounded_formula v f₂ dvector.nil)) := 
  by {rw[bd_biimp], tidy}

@[simp] lemma realize_term_remove_irrel {n : ℕ} {L : Language} {S : Structure L} {v : dvector ↥S (n+1)} {j : fin n} {k : ℕ} {p : k > j} : realize_bounded_term v ((lift_bounded_term_at (bd_var j : bounded_term L n) 1 k) ) dvector.nil = realize_bounded_term (dvector.remove_mth k v)  (bd_var j) dvector.nil :=
begin
sorry
end

set_option trace.check true
 
@[simp] lemma lift_realize_term  {L : Language} {S : Structure L} : ∀ {n : ℕ} {k : ℕ} {l : ℕ} {v : dvector ↥S (n+1)} {t: bounded_preterm L (n) l}, realize_bounded_term v (lift_bounded_term_at t 1 k) = realize_bounded_term (dvector.remove_mth k v) t 
  | n k 0 v (bd_var x) := sorry
  | n k l v (bd_func f) := sorry
  | _ _ _ _ _ := sorry
end
@[simp]lemma lift_realize_formula {n : ℕ} {k : ℕ} { l : ℕ}{L : Language} {S : Structure L}  { v : dvector ↥S (n+1)} { u : dvector ↥S l}: ∀ {f : bounded_preformula L n l}, realize_bounded_formula v ( f ↑' 1 # k) u = realize_bounded_formula (dvector.remove_mth k v) f u :=
begin
  intros f,
  induction f,
  simp*,
  simp [lift_bounded_formula_at], sorry
end

@[simp]lemma Set'_realize_subset_2 : ∀ x y : Set, @realize_bounded_formula L_ZFC Set' 2 0 (x :: y :: dvector.nil) subset  dvector.nil  = Set.subset x y:=
begin
  simp [subset], intros, conv {to_lhs, change ∀ z, z ∈ x → z ∈ y}, rw [Set.subset]
end

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
  unfold axiom_of_powerset Th small subset,
    simp only [fol.realize_bounded_formula_ex, fol.bounded_preformula.cast,
    realize_bounded_formula_biimp, fol.lift_bounded_formula_at,
    fol.realize_bounded_formula, fol.bounded_preformula.cast_rfl,
    set.mem_set_of_eq, Set'_mem_mem, fol.realize_bounded_term,
    dvector.nth],
  intro x, refine ⟨Set.powerset x, _⟩, apply Set.mem_powerset
end

lemma Set'_models_choice : axiom_of_choice ∈ Th Set' :=
begin
  dsimp[Th, axiom_of_choice, fn_domain],
end

lemma Set'_models_infinity : axiom_of_infinity ∈ Th Set' :=
begin
simp [has_mem.mem, set.mem, Th, set_of, axiom_of_infinity,satisfied_in], 
sorry
end

lemma Set'_models_replacement: ∀ c : bounded_formula L_ZFC 2, axiom_of_replacement c ∈ Th Set' := sorry

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
