import .bvm .bvm_extras .pSet_ordinal

open lattice

universe u

local infix ` ⟹ `:65 := lattice.imp

local infix ` ⇔ `:50 := lattice.biimp

local infix `≺`:75 := (λ x y, -(bSet.larger_than x y))

local infix `≼`:75 := (λ x y, bSet.injects_into x y)

namespace bSet

section lemmas
variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹] {Γ : 𝔹}

lemma prod_subset {x₁ x₂ y₁ y₂ : bSet 𝔹} (H_sub₁ : Γ ≤ x₁ ⊆ᴮ x₂) (H_sub₂ : Γ ≤ y₁ ⊆ᴮ y₂) : Γ ≤ prod x₁ y₁ ⊆ᴮ prod x₂ y₂ :=
begin
  rw subset_unfold', bv_intro pr, bv_imp_intro Hpr,
  rw mem_prod_iff₂ at Hpr ⊢, rcases Hpr with ⟨v,Hv,w,Hw,H_eq⟩,
  have Hv' := mem_of_mem_subset H_sub₁ Hv,
  have Hw' := mem_of_mem_subset H_sub₂ Hw,
  exact ⟨v,‹_›,w,‹_›,‹_›⟩
end

lemma prod_subset_left {x₁ x₂ y : bSet 𝔹} (H_sub : Γ ≤ x₁ ⊆ᴮ x₂) : Γ ≤ prod x₁ y ⊆ᴮ prod x₂ y :=
prod_subset H_sub subset_self

lemma prod_subset_right {x y₁ y₂ : bSet 𝔹} (H_sub : Γ ≤ y₁ ⊆ᴮ y₂) : Γ ≤ prod x y₁ ⊆ᴮ prod x y₂ :=
prod_subset subset_self H_sub

end lemmas

section inj_inverse_surj
variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹] {x y f : bSet 𝔹} {Γ : 𝔹}
  (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f)

lemma inj_inverse.is_total_surj (H_surj : Γ ≤ is_surj x y f) : Γ ≤ is_total y x (inj_inverse H_func H_inj) :=
begin
  have := bv_symm (image_eq_codomain_of_surj H_surj),
  apply @bv_rw' _ _ _ _ _ this (λ z, is_total z x (inj_inverse H_func H_inj)), simp,
  apply inj_inverse.is_total
end

lemma inj_inverse.is_function_surj (H_surj : Γ ≤ is_surj x y f) : Γ ≤ is_function y x (inj_inverse H_func H_inj) :=
begin
  have := bv_symm (image_eq_codomain_of_surj H_surj),
  apply @bv_rw' _ _ _ _ _ this (λ z, is_function z x (inj_inverse H_func H_inj)), simp,
  apply inj_inverse.is_function
end

lemma inj_inverse.is_surj_surj (H_surj : Γ ≤ is_surj x y f) : Γ ≤ is_surj y x (inj_inverse H_func H_inj) :=
begin
  apply @bv_rw' _ _ _ _ _ (bv_symm (image_eq_codomain_of_surj H_surj))
          (λ z, is_surj z x (inj_inverse H_func H_inj)), simp,
  apply inj_inverse.is_surj
end

end inj_inverse_surj

section Ord
variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹] {Γ : 𝔹}

lemma subset_of_mem_Ord {x y : bSet 𝔹} {Γ} (H_mem : Γ ≤ x ∈ᴮ y) (H_Ord : Γ ≤ Ord y) : Γ ≤ x ⊆ᴮ y :=
subset_of_mem_transitive (bv_and.right ‹_›) ‹_›

lemma mem_of_mem_Ord {x y z : bSet 𝔹} {Γ} (H_mem : Γ ≤ x ∈ᴮ y) (H_mem' : Γ ≤ y ∈ᴮ z) (H_ord₂ : Γ ≤ Ord z) : Γ ≤ x ∈ᴮ z :=
begin
  refine mem_of_mem_subset _ H_mem, apply subset_of_mem_Ord; from ‹_›
end

@[reducible]lemma Ord_max {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) : bSet 𝔹 :=
succ (binary_union x y)

lemma transitive_union {u : bSet 𝔹} {Γ : 𝔹} (Hu : Γ ≤ ⨅z, z ∈ᴮ u ⟹ is_transitive z) : Γ ≤ is_transitive (bv_union u) :=
begin
  bv_intro x, bv_imp_intro H_mem, rw mem_bv_union_iff at H_mem,
  bv_cases_at H_mem y Hy, bv_split_at Hy,
  rw subset_unfold', bv_intro w, bv_imp_intro Hw,
  rw mem_bv_union_iff, apply bv_use y, refine le_inf ‹_› _,
  simp only [is_transitive] at Hu,
  exact mem_of_mem_subset (Hu y ‹_› x ‹_›) ‹_›
end

lemma transitive_binary_inter {x y : bSet 𝔹} {Γ} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) : Γ ≤ is_transitive (x ∩ᴮ y) :=
begin
  bv_intro z, bv_imp_intro H_mem, rw mem_binary_inter_iff at H_mem, cases H_mem with H_mem₁ H_mem₂,
    rw subset_unfold', bv_intro w, bv_imp_intro Hw, rw mem_binary_inter_iff, refine ⟨_,_⟩,
      { have := (bv_and.right H₁), unfold is_transitive at this, exact mem_of_mem_subset (this z ‹_›) ‹_› },
      { have := (bv_and.right H₂), unfold is_transitive at this, exact mem_of_mem_subset (this z ‹_›) ‹_› }
end

lemma epsilon_trichotomy_binary_inter {x y : bSet 𝔹} {Γ} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) : Γ ≤ epsilon_trichotomy (x ∩ᴮ y) :=
begin
  bv_intro w, bv_imp_intro Hw_mem, bv_intro z, bv_imp_intro Hz_mem,
  rw mem_binary_inter_iff at Hw_mem Hz_mem, cases Hz_mem with Hz_mem_x Hz_mem_y,
  cases Hw_mem with Hw_mem_x Hw_mem_y,
  exact epsilon_trichotomy_of_Ord Hw_mem_x Hz_mem_x ‹_›
end

lemma epsilon_well_founded_binary_inter {x y : bSet 𝔹} {Γ} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) : Γ ≤ epsilon_well_founded (x ∩ᴮ y) :=
begin
  bv_intro w, bv_imp_intro Hw_sub, bv_imp_intro H_nonempty,
  rcases subset_binary_inter_iff.mp Hw_sub with ⟨Hw_sub₁, Hw_sub₂⟩,
  exact (bv_and.right (bv_and.left H₁) w) Hw_sub₁ ‹_›,
end

lemma Ord_binary_inter {x y : bSet 𝔹} {Γ} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) : Γ ≤ Ord (binary_inter x y) :=
begin
  refine le_inf _ _,
    { from le_inf (epsilon_trichotomy_binary_inter H₁ H₂) (epsilon_well_founded_binary_inter ‹_› ‹_›) },
    { bv_intro z, bv_imp_intro H_mem, rw mem_binary_inter_iff at H_mem, cases H_mem with H_mem₁ H_mem₂,
      rw subset_unfold', bv_intro w, bv_imp_intro Hw, rw mem_binary_inter_iff, refine ⟨_,_⟩,
        { have := (bv_and.right H₁), unfold is_transitive at this, exact mem_of_mem_subset (this z ‹_›) ‹_› },
        { have := (bv_and.right H₂), unfold is_transitive at this, exact mem_of_mem_subset (this z ‹_›) ‹_› }}
end

section compl

def compl (x y : bSet 𝔹) := comprehend (λ z, - (z ∈ᴮ y)) x

lemma compl_subset {x y : bSet 𝔹} : Γ ≤ compl x y ⊆ᴮ x :=
by {rw compl, apply comprehend_subset, simp}

lemma mem_compl_iff {x y : bSet 𝔹} {z} : Γ ≤ z ∈ᴮ compl x y ↔ (Γ ≤ z ∈ᴮ x ∧ Γ ≤ -(z ∈ᴮ y)) :=
begin
  unfold compl,
  refine ⟨_,_⟩; intro H,
    { rw mem_comprehend_iff₂ at H, refine ⟨_,_⟩,
      { bv_cases_at H w Hw, bv_split, bv_split, bv_cc },
      { bv_cases_at H w Hw, bv_split, bv_split, apply bv_rw' Hw_right_left, simp, from ‹_› },
      { simp }  },
    { rw mem_comprehend_iff₂, cases H with H₁ H₂, apply bv_use z,
      refine le_inf ‹_› (le_inf bv_refl _), from ‹_›, simp }
end

lemma compl_empty_of_subset {x y : bSet 𝔹} (H_sub : Γ ≤ x ⊆ᴮ y) : Γ ≤ compl x y =ᴮ ∅ :=
begin
  apply bv_by_contra, bv_imp_intro H_contra, rw nonempty_iff_exists_mem at H_contra, bv_cases_at H_contra w Hw,
  rw mem_compl_iff at Hw, cases Hw with Hw₁ Hw₂,
  suffices : Γ_2 ≤ w ∈ᴮ y, by bv_contradiction,
  from mem_of_mem_subset ‹_› ‹_›
end

lemma nonempty_compl_of_ne {x y : bSet 𝔹} (H_ne : Γ ≤ - ( x=ᴮ y)) : Γ ≤ (- ((compl x y) =ᴮ ∅)) ⊔ (- ((compl y x) =ᴮ ∅)) :=
begin
  rw bv_eq_unfold' at H_ne, simp only with bv_push_neg at H_ne, bv_or_elim_at H_ne,
    { refine bv_or_left _, rw nonempty_iff_exists_mem, bv_cases_at H_ne.left z Hz, apply bv_use z,
      rw mem_compl_iff, bv_split, from ⟨‹_›,‹_›⟩ },
    { refine bv_or_right _, rw nonempty_iff_exists_mem, bv_cases_at H_ne.right z Hz, apply bv_use z,
      rw mem_compl_iff, bv_split, from ⟨‹_›,‹_›⟩ }
end

end compl

lemma eq_iff_not_mem_of_Ord {x y z : bSet 𝔹} (H_mem₁ : Γ ≤ x ∈ᴮ z) (H_mem₂ : Γ ≤ y ∈ᴮ z) (H_ord : Γ ≤ Ord z) : Γ ≤ x =ᴮ y ↔ (Γ ≤ -(x ∈ᴮ y) ∧ Γ ≤ -(y ∈ᴮ x)) :=
begin
  have H_tri := epsilon_trichotomy_of_Ord H_mem₁ H_mem₂ H_ord,
  refine ⟨_,_⟩; intro H,
    { refine ⟨_,_⟩,
      { apply bv_rw' H, simp, rw ←imp_bot, bv_imp_intro H', from bot_of_mem_self' ‹_› },
      { apply bv_rw' H, simp, rw ←imp_bot, bv_imp_intro H', from bot_of_mem_self' ‹_› }},
    { cases H with H₁ H₂, bv_or_elim_at H_tri, bv_or_elim_at H_tri.left,
        { from ‹_› },
        { apply bv_exfalso, bv_contradiction },
        { apply bv_exfalso, bv_contradiction }}
end

lemma Ord.lt_of_ne_and_le {x y : bSet 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) (H_ne : Γ ≤ -(x =ᴮ y)) (H_le : Γ ≤ x ⊆ᴮ y) : Γ ≤ x ∈ᴮ y :=
begin
  have H_compl_nonempty : Γ ≤ - (compl y x =ᴮ ∅),
    by { have this₁ := nonempty_compl_of_ne H_ne,
         have this₂ := compl_empty_of_subset H_le,
         bv_or_elim_at this₁,
           { apply bv_exfalso, from bv_absurd _ this₂ ‹_› },
           { from ‹_› } },
  have H_ex_min := bSet_axiom_of_regularity _ H_compl_nonempty,
  bv_cases_at H_ex_min z Hz, bv_split_at Hz,
  cases mem_compl_iff.mp Hz_left with Hz₁ Hz₂,
  suffices H_eq : Γ_1 ≤ x =ᴮ z, by bv_cc,
  rw bv_eq_unfold', refine le_inf _ _,
         { bv_intro a, bv_imp_intro Ha, have this' := epsilon_trichotomy_of_Ord (mem_of_mem_subset H_le Ha) ‹_› ‹_›,
           bv_or_elim_at this', bv_or_elim_at this'.left,
             { apply bv_exfalso, exact bv_absurd (z ∈ᴮ x) (by bv_cc) ‹_› },
             { from ‹_› },
             { apply bv_exfalso, refine bv_absurd (z ∈ᴮ x) _ ‹_›,
               apply mem_of_mem_Ord this'.right ‹_› ‹_› }},
         { bv_intro a, bv_imp_intro Ha, apply bv_by_contra, bv_imp_intro H_contra,
           have Ha' : Γ_3 ≤ a ∈ᴮ y,
             by {refine mem_of_mem_Ord Ha ‹_› H₂, },
           have : Γ_3 ≤ a ∈ᴮ y ∧ Γ_3 ≤ -(a ∈ᴮ x) := ⟨‹_›,‹_›⟩,
           rw ←mem_compl_iff at this,
           refine bv_absurd _ Ha _,
           exact Hz_right a ‹_› }
end

lemma Ord.le_or_le {x y : bSet 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) : Γ ≤ x ⊆ᴮ y ⊔ y ⊆ᴮ x :=
begin
  let w := x ∩ᴮ y,
  have w_Ord : Γ ≤ Ord w := Ord_binary_inter H₁ H₂,
  have : Γ ≤ w =ᴮ x ⊔ w =ᴮ y,
    by { apply bv_by_contra, bv_imp_intro H_contra, simp only with bv_push_neg at H_contra,
         suffices : Γ_1 ≤ w ∈ᴮ x ∧ Γ_1 ≤ w ∈ᴮ y,
           by { suffices : Γ_1 ≤ w ∈ᴮ w, from bot_of_mem_self' ‹_›,
                rwa mem_binary_inter_iff }, bv_split_at H_contra,
                refine ⟨_,_⟩,
                  { apply Ord.lt_of_ne_and_le w_Ord, repeat {assumption}, from binary_inter_subset_left },
                  { apply Ord.lt_of_ne_and_le w_Ord, repeat {assumption}, from binary_inter_subset_right }},
  bv_or_elim_at this,
    { refine bv_or_left _, apply bv_rw' (bv_symm this.left), simp,
      exact binary_inter_subset_right },
    { refine bv_or_right _, apply bv_rw' (bv_symm this.right), simp,
      exact binary_inter_subset_left }
end

lemma Ord.trichotomy {x y : bSet 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) : Γ ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x :=
begin
  have := Ord.le_or_le H₁ H₂,
  bv_or_elim_at this,
    { bv_cases_on x =ᴮ y,
       { from bv_or_left (bv_or_left ‹_›) },
       { refine bv_or_left (bv_or_right _), apply Ord.lt_of_ne_and_le, repeat {assumption} }},
    { bv_cases_on x =ᴮ y,
       { from bv_or_left (bv_or_left ‹_›) },
       { refine bv_or_right _, rw bv_eq_symm at H.right, apply Ord.lt_of_ne_and_le, repeat {assumption} }}
end

lemma Ord.eq_iff_not_mem {x y : bSet 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) : Γ ≤ x =ᴮ y  ↔ (Γ ≤ -(x ∈ᴮ y) ∧ Γ ≤ -(y ∈ᴮ x)) :=
begin
  refine ⟨_,_⟩; intro H,
    { refine ⟨_,_⟩,
        { rw ←imp_bot, bv_imp_intro H_contra, apply bot_of_mem_self', show bSet 𝔹, from y,
          bv_cc  },
        { rw ←imp_bot, bv_imp_intro H_contra, apply bot_of_mem_self', show bSet 𝔹, from y,
          bv_cc } },
    { cases H with H₁' H₂', have := Ord.trichotomy H₁ H₂,
      bv_or_elim_at this, bv_or_elim_at this.left,
      all_goals { assumption <|> {apply bv_exfalso; bv_contradiction} } }
end

lemma Ord.eq_of_not_mem {x y : bSet 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) (H_nmem₁ : Γ ≤ -(x ∈ᴮ y)) (H_nmem₂ : Γ ≤ -(y ∈ᴮ x)) : Γ ≤ x =ᴮ y :=
by { rw Ord.eq_iff_not_mem; simp* }

lemma Ord.le_iff_lt_or_eq {x y : bSet 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) : Γ ≤ x ⊆ᴮ y ↔ (Γ ≤ x ∈ᴮ y ⊔ x =ᴮ y) :=
begin
  refine ⟨_,_⟩; intro H,
    { bv_cases_on x =ᴮ y,
        { exact bv_or_right ‹_› },
        { refine bv_or_left _, apply Ord.lt_of_ne_and_le ‹_› H₂ ‹_› ‹_› } },
    { bv_or_elim_at H,
      { from subset_of_mem_Ord ‹_› ‹_› },
      { apply bv_rw' H.right, simp, from subset_self }}
end

lemma Ord.lt_of_not_le {x y : bSet 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) : Γ ≤ -(x ⊆ᴮ y) → Γ ≤ y ∈ᴮ x :=
begin
  intro H_not_le, apply bv_by_contra, bv_imp_intro H_contra, rw ←imp_bot at H_not_le, refine H_not_le _,
  rw Ord.le_iff_lt_or_eq,
    { have := Ord.trichotomy H₁ H₂,
      bv_or_elim_at this,
        { rwa sup_comm },
        { apply bv_exfalso, bv_contradiction } },
    { from ‹_› },
    { from ‹_› }
end

lemma Ord.resolve_lt {x y : bSet 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) : Γ ≤ -(x ∈ᴮ y) → Γ ≤ (y ∈ᴮ x) ⊔ (y =ᴮ x) :=
begin
  intro H_not_mem, have := Ord.trichotomy H₁ H₂,
  bv_or_elim_at this, bv_or_elim_at this.left,
    { from bv_or_right (bv_symm ‹_›) },
    { from bv_exfalso (by bv_contradiction) },
    { from bv_or_left ‹_› }
end

lemma epsilon_trichotomy_of_sub_Ord {Γ : 𝔹} (u : bSet 𝔹) (H_ord : Γ ≤ ⨅ x, x ∈ᴮ u ⟹ Ord x)
  : Γ ≤ (⨅y, y∈ᴮ u ⟹ (⨅z, z ∈ᴮ u ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y))) :=
begin
  bv_intro y, bv_imp_intro Hy, bv_intro z, bv_imp_intro Hz,
  have H₁ : Γ_2 ≤ Ord y := H_ord y ‹_›,
  have H₂ : Γ_2 ≤ Ord z := H_ord z ‹_›,
  exact Ord.trichotomy H₁ H₂
end

lemma epsilon_wf_of_sub_Ord {Γ : 𝔹} (u : bSet 𝔹) (H_ord : Γ ≤ ⨅ x, x ∈ᴮ u ⟹ Ord x)
  : Γ ≤ (⨅x, x ⊆ᴮ u ⟹ (- (x =ᴮ ∅) ⟹ ⨆y, y∈ᴮ x ⊓ (⨅z', z' ∈ᴮ x ⟹ (- (z' ∈ᴮ y))))) :=
begin
  bv_intro x, bv_imp_intro Hsub, bv_imp_intro H_nonempty,
  exact bSet_axiom_of_regularity _ H_nonempty,
end

def exists_two (η : bSet 𝔹) : 𝔹 := (⨅x, x ∈ᴮ η ⟹ ⨆ z, z ∈ᴮ η ⊓ (x ∈ᴮ z ⊔ z ∈ᴮ x))

@[simp]lemma B_ext_exists_two : B_ext (exists_two : bSet 𝔹 → 𝔹) :=
begin
  unfold B_ext, unfold exists_two, change B_ext _, simp
end

lemma one_mem_of_not_zero_and_not_one {η : bSet 𝔹} {Γ : 𝔹} (H_ord : Γ ≤ Ord η) (H_not_zero : Γ ≤ -(η =ᴮ 0)) (H_not_one : Γ ≤ -(η =ᴮ 1)) : Γ ≤ 1 ∈ᴮ η :=
begin
  have := Ord.trichotomy (H_ord) Ord_one,
  bv_or_elim_at this, bv_or_elim_at this.left,
    { apply bv_exfalso, bv_contradiction },
    { suffices : Γ_2 ≤ η =ᴮ 0, by apply bv_exfalso; bv_contradiction,
      exact eq_zero_of_mem_one this.left.right },
    { from ‹_› }
end

lemma exists_two_iff { η : bSet 𝔹 } { Γ : 𝔹 } (H_ord : Γ ≤ Ord η): Γ ≤ exists_two η ↔ Γ ≤ (- (η =ᴮ 1)) :=
begin
  refine ⟨_,_⟩; intro H,
    { rw ←imp_bot, bv_imp_intro H_contra,
      have : Γ_1 ≤ 0 ∈ᴮ η,
        by { apply bv_rw' H_contra, simp, simp },
      unfold exists_two at H, replace H := H (0 : bSet 𝔹) ‹_›,
      bv_cases_at H w Hw, bv_split_at Hw, bv_or_elim_at Hw_right,
      { suffices : Γ_3 ≤ 0 ∈ᴮ 0,
          by exact bot_of_mem_self' ‹_›,
        suffices : Γ_3 ≤ w =ᴮ 0,
          by bv_cc,
        exact eq_zero_of_mem_one (by bv_cc) },
      { suffices : Γ_3 ≤ 0 ∈ᴮ 0,
          by exact bot_of_mem_self' ‹_›,
        suffices : Γ_3 ≤ w =ᴮ 0,
          by bv_cc,
        exact eq_zero_of_mem_one (by bv_cc) } },
  { bv_cases_on η =ᴮ 0,
      { apply bv_rw' H_1.left, simp, apply bv_rw' zero_eq_empty, simp, apply forall_empty },
      { suffices : Γ_1 ≤ 1 ∈ᴮ η,
          by { bv_intro z, bv_imp_intro Hz_mem,
               have this' := Ord.trichotomy (Ord_of_mem_Ord Hz_mem H_ord) (Ord_one),
               bv_or_elim_at this',
               bv_or_elim_at this'.left,
                 { apply bv_use (0 : bSet 𝔹), refine le_inf _ (bv_or_right _),
                   { exact mem_of_mem_Ord (zero_mem_one) ‹_› ‹_› },
                   { apply bv_rw' ‹_ ≤ z =ᴮ 1›, simp, exact zero_mem_one } },
                 { apply bv_use (1 : bSet 𝔹), exact le_inf ‹_› (bv_or_left ‹_›) },
                 { apply bv_use (1 : bSet 𝔹), refine le_inf ‹_› (bv_or_right ‹_›) }},
        exact one_mem_of_not_zero_and_not_one ‹_› ‹_› ‹_› }}
end

end Ord

section eps_iso
variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

@[reducible]def strong_eps_hom (x y f : bSet 𝔹) : 𝔹 := (⨅ z₁, z₁ ∈ᴮ x ⟹ ⨅ z₂, z₂ ∈ᴮ x ⟹ ⨅ w₁, w₁ ∈ᴮ y ⟹ ⨅ w₂, w₂ ∈ᴮ y ⟹ (pair z₁ w₁ ∈ᴮ f ⟹ (pair z₂ w₂ ∈ᴮ f ⟹ (z₁ ∈ᴮ z₂ ⇔ w₁ ∈ᴮ w₂))))

lemma strong_eps_hom_iff {x y f : bSet 𝔹} {Γ} : Γ ≤ strong_eps_hom x y f ↔ ∀ {Γ'} (H_le : Γ' ≤ Γ), ∀ z₁ (Hz₁_mem : Γ' ≤ z₁ ∈ᴮ x) (z₂) (Hz₂_mem : Γ' ≤ z₂ ∈ᴮ x) (w₁) (Hw₁_mem : Γ' ≤ w₁ ∈ᴮ y) (w₂) (Hw₂_mem : Γ' ≤ w₂ ∈ᴮ y) (Hpr₁_mem : Γ' ≤ pair z₁ w₁ ∈ᴮ f) (Hpr₂_mem : Γ' ≤ pair z₂ w₂ ∈ᴮ f), Γ' ≤ z₁ ∈ᴮ z₂ ↔ Γ' ≤ w₁ ∈ᴮ w₂ :=
begin
  refine ⟨_,_⟩; intro H,
    { intros, have := (le_trans H_le H) z₁ ‹_› z₂ ‹_› w₁ ‹_› w₂ ‹_› ‹_› ‹_›,
       rw bv_biimp_iff at this, apply this, refl },
    { rw strong_eps_hom, bv_intro z₁, bv_imp_intro' Hz₁_mem, bv_intro z₂, bv_imp_intro Hz₂_mem,
  bv_intro w₁, bv_imp_intro Hw₁_mem, bv_intro w₁, bv_imp_intro Hw₂_mem, bv_imp_intro Hpr₁_mem,
  bv_imp_intro HPr₂_mem, rw bv_biimp_iff, intros Γ' H_Γ', apply_all le_trans H_Γ',
  apply H,
  refine le_trans H_Γ' (by { dsimp[Γ_6,Γ_5,Γ_4,Γ_3,Γ_2,Γ_1], tidy_context }),
  repeat { assumption } }
end

lemma strong_eps_hom_unfold {x y f : bSet 𝔹} {Γ} : Γ ≤ strong_eps_hom x y f → ∀ z₁ (Hz₁_mem : Γ ≤ z₁ ∈ᴮ x) (z₂) (Hz₂_mem : Γ ≤ z₂ ∈ᴮ x) (w₁) (Hw₁_mem : Γ ≤ w₁ ∈ᴮ y) (w₂) (Hw₂_mem : Γ ≤ w₂ ∈ᴮ y) (Hpr₁_mem : Γ ≤ pair z₁ w₁ ∈ᴮ f) (Hpr₂_mem : Γ ≤ pair z₂ w₂ ∈ᴮ f), Γ ≤ z₁ ∈ᴮ z₂ ↔ Γ ≤ w₁ ∈ᴮ w₂ := λ H,
begin
  intros, have := H z₁ ‹_› z₂ ‹_› w₁ ‹_› w₂ ‹_› ‹_› ‹_›,
  rw bv_biimp_iff at this, apply this, refl
end

def eps_iso (x y f : bSet 𝔹) : 𝔹 := is_function x y f ⊓ (strong_eps_hom x y f) ⊓ is_surj x y f

lemma is_surj_of_eps_iso {x y f : bSet 𝔹} {Γ} (H_eps_iso : Γ ≤ eps_iso x y f) : Γ ≤ is_surj x y f :=
bv_and.right ‹_›

lemma is_function_of_eps_iso {x y f : bSet 𝔹} {Γ} (H_eps_iso : Γ ≤ eps_iso x y f) : Γ ≤ is_function x y f :=
bv_and.left (bv_and.left ‹_›)

lemma strong_eps_hom_of_eps_iso {x y f : bSet 𝔹} {Γ} (H_eps_iso : Γ ≤ eps_iso x y f) : Γ ≤ strong_eps_hom x y f :=
by {bv_split_at H_eps_iso, from bv_and.right ‹_›}

lemma eps_iso_mem {x y f z₁ z₂ : bSet 𝔹} {Γ} (H₂ : Γ ≤ eps_iso x y f) (H_mem : Γ ≤ z₁ ∈ᴮ x) (H_mem' : Γ ≤ z₂ ∈ᴮ x) (H_mem'' : Γ ≤ z₁ ∈ᴮ z₂) {w₁} (H_mem''' : Γ ≤ w₁ ∈ᴮ y) (H_mem_pr₁ : Γ ≤ pair z₁ w₁ ∈ᴮ f) {w₂} (H_mem'''' : Γ ≤ w₂ ∈ᴮ y) (H_mem_pr₂ : Γ ≤ pair z₂ w₂ ∈ᴮ f) : Γ ≤ w₁ ∈ᴮ w₂ :=
by rwa ←(strong_eps_hom_unfold (strong_eps_hom_of_eps_iso ‹_›) z₁ ‹_› z₂ ‹_› w₁ ‹_› w₂ ‹_› ‹_› ‹_›)

lemma eps_iso_mem' {x y f z₁ z₂ : bSet 𝔹} {Γ} (H₂ : Γ ≤ eps_iso x y f) (H_mem : Γ ≤ z₁ ∈ᴮ x) (H_mem' : Γ ≤ z₂ ∈ᴮ x) {w₁} (H_mem''' : Γ ≤ w₁ ∈ᴮ y) (H_mem_pr₁ : Γ ≤ pair z₁ w₁ ∈ᴮ f) {w₂} (H_mem'''' : Γ ≤ w₂ ∈ᴮ y) (H_mem_pr₂ : Γ ≤ pair z₂ w₂ ∈ᴮ f) (H_mem'' : Γ ≤ w₁ ∈ᴮ w₂) : Γ ≤ z₁ ∈ᴮ z₂ :=
by rwa (strong_eps_hom_unfold (strong_eps_hom_of_eps_iso ‹_›) z₁ ‹_› z₂ ‹_› w₁ ‹_› w₂ ‹_› ‹_› ‹_›)

lemma eps_iso_not_mem {x y f z₁ z₂ : bSet 𝔹} {Γ} (H₂ : Γ ≤ eps_iso x y f) (H_mem : Γ ≤ z₁ ∈ᴮ x) (H_mem' : Γ ≤ z₂ ∈ᴮ x) (H_mem'' : Γ ≤ -(z₁ ∈ᴮ z₂)) {w₁} (H_mem''' : Γ ≤ w₁ ∈ᴮ y) (H_mem_pr₁ : Γ ≤ pair z₁ w₁ ∈ᴮ f) {w₂} (H_mem'''' : Γ ≤ w₂ ∈ᴮ y) (H_mem_pr₂ : Γ ≤ pair z₂ w₂ ∈ᴮ f) : Γ ≤ -(w₁ ∈ᴮ w₂) :=
begin
  rw ←imp_bot at ⊢ H_mem'', bv_imp_intro Hw_mem, refine H_mem'' _,
  rwa (strong_eps_hom_unfold (strong_eps_hom_of_eps_iso ‹_›) z₁ ‹_› z₂ ‹_› w₁ ‹_› w₂ ‹_› ‹_› ‹_›)
end

lemma eps_iso_not_mem' {x y f z₁ z₂ : bSet 𝔹} {Γ} (H₂ : Γ ≤ eps_iso x y f) (H_mem : Γ ≤ z₁ ∈ᴮ x) (H_mem' : Γ ≤ z₂ ∈ᴮ x) {w₁} (H_mem''' : Γ ≤ w₁ ∈ᴮ y) (H_mem_pr₁ : Γ ≤ pair z₁ w₁ ∈ᴮ f) {w₂} (H_mem'''' : Γ ≤ w₂ ∈ᴮ y) (H_mem_pr₂ : Γ ≤ pair z₂ w₂ ∈ᴮ f) (H_mem'' : Γ ≤ -(w₁ ∈ᴮ w₂)) : Γ ≤ -(z₁ ∈ᴮ z₂) :=
begin
  rw ←imp_bot at ⊢ H_mem'', bv_imp_intro Hw_mem, refine H_mem'' _,
  rwa ←(strong_eps_hom_unfold (strong_eps_hom_of_eps_iso ‹_›) z₁ ‹_› z₂ ‹_› w₁ ‹_› w₂ ‹_› ‹_› ‹_›)
end

lemma eps_iso_inj_of_Ord {x y f : bSet 𝔹} {Γ} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) (H₃ : Γ ≤ eps_iso x y f) : Γ ≤ is_inj f :=
begin
  bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂, bv_imp_intro H,
  bv_split_at H, bv_split_at H_left,
  have H_function := is_function_of_eps_iso ‹_›,
  have Hw₁_mem : Γ_1 ≤ w₁ ∈ᴮ x := mem_domain_of_is_function ‹_› ‹_›,
  have Hw₂_mem : Γ_1 ≤ w₂ ∈ᴮ x := mem_domain_of_is_function ‹_› ‹_›,
  have Hv₁_mem : Γ_1 ≤ v₁ ∈ᴮ y := mem_codomain_of_is_function ‹_› ‹_›,
  have Hv₂_mem : Γ_1 ≤ v₂ ∈ᴮ y := mem_codomain_of_is_function ‹_› ‹_›,
  have Hw₁_ord : Γ_1 ≤ Ord w₁ := Ord_of_mem_Ord ‹_› ‹_›,
  have Hw₂_ord : Γ_1 ≤ Ord w₂ := Ord_of_mem_Ord ‹_› ‹_›,
  have Hv₁_ord : Γ_1 ≤ Ord v₁ := Ord_of_mem_Ord ‹_› ‹_›,
  have Hv₂_ord : Γ_1 ≤ Ord v₂ := Ord_of_mem_Ord ‹_› ‹_›,
  suffices : Γ_1 ≤ - (w₁ ∈ᴮ w₂) ∧ Γ_1 ≤ -(w₂ ∈ᴮ w₁),
    by { refine Ord.eq_of_not_mem ‹_› ‹_› this.left this.right } ,
  rw Ord.eq_iff_not_mem at H_right,
    { cases H_right with H_nmem₁ H_nmem₂, refine ⟨_,_⟩,
      { exact eps_iso_not_mem' ‹_› Hw₁_mem Hw₂_mem Hv₁_mem ‹_› Hv₂_mem ‹_› ‹_›,  },
      { exact eps_iso_not_mem' ‹_› Hw₂_mem Hw₁_mem Hv₂_mem  ‹_› Hv₁_mem ‹_› ‹_› } },
    { from ‹_› },
    { from ‹_› }
end

def eps_iso_inv {x y f : bSet 𝔹} {Γ} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) (H₃ : Γ ≤ eps_iso x y f) : bSet 𝔹 := inj_inverse (is_func'_of_is_function (bv_and.left $ bv_and.left H₃)) (eps_iso_inj_of_Ord H₁ H₂ H₃)

lemma eps_iso_inv_surj {x y f : bSet 𝔹} {Γ} {H₁ : Γ ≤ Ord x} {H₂ : Γ ≤ Ord y} {H₃ : Γ ≤ eps_iso x y f} : Γ ≤ is_surj y x (eps_iso_inv H₁ H₂ H₃) :=
inj_inverse.is_surj_surj _ _ (is_surj_of_eps_iso ‹_›)

lemma eps_iso_inv_is_function {x y f : bSet 𝔹} {Γ} {H₁ : Γ ≤ Ord x} {H₂ : Γ ≤ Ord y} {H₃ : Γ ≤ eps_iso x y f} : Γ ≤ is_function y x (eps_iso_inv H₁ H₂ H₃) :=
begin
  apply inj_inverse.is_function_surj, from is_surj_of_eps_iso ‹_›
end

lemma eps_iso_inv_strong_eps_hom {x y f : bSet 𝔹} {Γ} {H₁ : Γ ≤ Ord x} {H₂ : Γ ≤ Ord y} {H₃ : Γ ≤ eps_iso x y f} : Γ ≤ strong_eps_hom y x (eps_iso_inv H₁ H₂ H₃) :=
begin
  have := (strong_eps_hom_of_eps_iso ‹_›),
  rw strong_eps_hom, bv_intro z₁, bv_imp_intro' Hz₁_mem, bv_intro z₂, bv_imp_intro Hz₂_mem,
  bv_intro w₁, bv_imp_intro Hw₁_mem, bv_intro w₂, bv_imp_intro Hw₂_mem, bv_imp_intro Hpr₁_mem,
  bv_imp_intro Hpr₂_mem, rw biimp_symm,
  have Hpr₁_mem' : Γ_6 ≤ pair w₁ z₁ ∈ᴮ f,
    by { erw mem_inj_inverse_iff at Hpr₁_mem, simp* },
  have Hpr₂_mem' : Γ_6 ≤ pair w₂ z₂ ∈ᴮ f,
    by { erw mem_inj_inverse_iff at Hpr₂_mem, simp* },
  rw strong_eps_hom_iff at this,
  rw bv_biimp_iff, intros Γ' H_Γ', apply_all le_trans H_Γ',
  specialize @this Γ' (by refine le_trans H_Γ' _; dsimp[Γ_6, Γ_5, Γ_4, Γ_3, Γ_2, Γ_1]; tidy_context),
  apply this, repeat {assumption}
end

lemma eps_iso_eps_iso_inv {x y f : bSet 𝔹} {Γ} {H₁ : Γ ≤ Ord x} {H₂ : Γ ≤ Ord y} {H₃ : Γ ≤ eps_iso x y f}
  : Γ ≤ eps_iso y x (eps_iso_inv H₁ H₂ H₃) :=
le_inf (le_inf eps_iso_inv_is_function eps_iso_inv_strong_eps_hom) (eps_iso_inv_surj)

lemma eps_iso_symm {x y : bSet 𝔹} {Γ} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) : (Γ ≤ ⨆ f, eps_iso x y f) ↔ (Γ ≤ ⨆ f, eps_iso y x f) :=
begin
  refine ⟨_,_⟩; intro H; bv_cases_at H f Hf,
    { apply bv_use (eps_iso_inv H₁ H₂ ‹_›), from eps_iso_eps_iso_inv },
    { apply bv_use (eps_iso_inv H₂ H₁ ‹_›), from eps_iso_eps_iso_inv }
end

lemma eps_iso_mono {x y z f : bSet 𝔹} {Γ} (H₁ : Γ ≤ Ord y) (H₂ : Γ ≤ z ⊆ᴮ y) (H₃ : Γ ≤ eps_iso y z f) (H₄ : Γ ≤ x ∈ᴮ y) (w' : bSet 𝔹) (Hw' : Γ ≤ pair x w' ∈ᴮ f) : Γ ≤ x ⊆ᴮ w' :=
begin
  suffices : Γ ≤ (comprehend (λ v, ⨅ w, pair v w ∈ᴮ f ⟹ w ∈ᴮ v) y) =ᴮ ∅,
    by { apply bv_by_contra, bv_imp_intro H_contra,
         suffices : Γ_1 ≤ -(comprehend (λ (v : bSet 𝔹), ⨅ (w : bSet 𝔹), pair v w ∈ᴮ f ⟹ w ∈ᴮ v) y =ᴮ ∅),
           by bv_contradiction,
         apply nonempty_of_exists_mem, apply bv_use x,
         rw mem_comprehend_iff₂, apply bv_use x,
         refine le_inf ‹_› (le_inf bv_refl _),
           { bv_intro w, bv_imp_intro Hw,
             have := Ord.lt_of_not_le _ _ H_contra,
             suffices : Γ_2 ≤ w =ᴮ w', by bv_cc,
             apply eq_of_is_function_of_eq (bv_and.left $ bv_and.left ‹_›), from (bv_refl : _ ≤ x =ᴮ x),
             from ‹_›, from ‹_›,
               { exact Ord_of_mem_Ord H₄ ‹_› },
               { refine Ord_of_mem_Ord (_ : _ ≤ w' ∈ᴮ y) ‹_›, refine mem_of_mem_subset H₂ _,
                 exact mem_codomain_of_is_function ‹_› (bv_and.left $ bv_and.left ‹_›) } },
           { simp }, },
  apply bv_by_contra, bv_imp_intro H_contra,
  replace H_contra := bSet_axiom_of_regularity _ H_contra,
  bv_cases_at H_contra a Ha, bv_split_at Ha,
  refine bv_absurd _ Ha_right _, simp only with bv_push_neg,
  have H_total := is_total_of_is_function (bv_and.left $ bv_and.left ‹_›),
  rw mem_comprehend_iff₂ at Ha_left,
    {bv_cases_at Ha_left a' Ha', bv_split_at Ha', bv_split_at Ha'_right,
    have a_mem_y : Γ_3 ≤ a ∈ᴮ y := by bv_cc,
    replace H_total := H_total a a_mem_y, bv_cases_at H_total wa Hwa, bv_split_at Hwa,
    have pair_a'_mem : Γ_4 ≤ pair a' wa ∈ᴮ f,
      by { apply bv_rw' (bv_symm Ha'_right_left), from B_ext_pair_mem_left, from ‹_› },
    have wa_mem_a : Γ_4 ≤ wa ∈ᴮ a,
      by { suffices : Γ_4 ≤ wa ∈ᴮ a', by bv_cc,
           from Ha'_right_right wa pair_a'_mem  },
    apply bv_use wa, refine le_inf _ _,
      { rw mem_comprehend_iff₂,
        { apply bv_use wa,
          have wa_mem_y : Γ_4 ≤ wa ∈ᴮ y,
            by { exact mem_of_mem_subset H₂ ‹_› },
          refine le_inf ‹_› (le_inf bv_refl _),
            { bv_intro wa', bv_imp_intro Hwa', refine eps_iso_mem ‹_› wa_mem_y a_mem_y wa_mem_a _ ‹_› ‹_› ‹_›,
              from mem_codomain_of_is_function Hwa' (bv_and.left $ bv_and.left H₃) } },
        { simp } },
      { from ‹_› } },
    { simp }
end

lemma eq_of_Ord_eps_iso_aux {x y : bSet 𝔹} {Γ} (Hx_ord : Γ ≤ Ord x) (Hy_ord : Γ ≤ Ord y) (H_eps_iso : Γ ≤ ⨆ f, eps_iso y x f) (H_mem : Γ ≤ x ∈ᴮ y) : Γ ≤ ⊥ :=
begin
  bv_cases_at H_eps_iso f Hf,
  have H_function := bv_and.left (bv_and.left Hf),
  have H_total := is_total_of_is_function H_function,
  replace H_total := H_total x ‹_›,
  bv_cases_at H_total w Hw, bv_split_at Hw,
  refine bot_of_mem_mem' _ _ _ Hw_left,
  have x_sub_y : Γ_2 ≤ x ⊆ᴮ y,
    by {apply subset_of_mem_Ord ‹_› ‹_›},
  suffices x_sub_w : Γ_2 ≤ x ⊆ᴮ w,
    by {rw Ord.le_iff_lt_or_eq at x_sub_w, bv_or_elim_at x_sub_w,
          {from ‹_›},
          { apply bv_exfalso,
            suffices : Γ_3 ≤ w ∈ᴮ w,
              by { exact bot_of_mem_self' ‹_› },
            bv_cc },
          from ‹_›, from Ord_of_mem_Ord ‹_› Hx_ord },
  apply eps_iso_mono Hy_ord x_sub_y, repeat { assumption  }
end

lemma eq_of_Ord_eps_iso {x y : bSet 𝔹} {Γ} (Hx_ord : Γ ≤ Ord x) (Hy_ord : Γ ≤ Ord y) (H_eps_iso : Γ ≤ ⨆ f, eps_iso x y f) : Γ ≤ x =ᴮ y :=
begin
  have := Ord.trichotomy Hx_ord Hy_ord,
  bv_or_elim_at this,
    { bv_or_elim_at this.left,
      { from ‹_› },
      { rw eps_iso_symm at H_eps_iso, apply bv_exfalso,
        from eq_of_Ord_eps_iso_aux Hx_ord Hy_ord ‹_› ‹_›, repeat {from ‹_›} }},
    { apply bv_exfalso, from eq_of_Ord_eps_iso_aux Hy_ord Hx_ord ‹_› ‹_› }
end

end eps_iso

end bSet
