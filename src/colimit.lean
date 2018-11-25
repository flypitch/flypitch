import .fol order tactic.tidy .to_mathlib .language_extension

/- The proper generality to do this is with directed categories as the indexing objects -/

/- We'll settle for directed types instead -/

local attribute [instance, priority 0] classical.prop_decidable

universes u v w

namespace colimit

-- def directed {ι : Sort v} (f : ι → α) := ∀x y, ∃z, f x ≼ f z ∧ f y ≼ f z

structure directed_type : Type (u+1) :=
  (carrier : Type u) (rel : carrier → carrier → Prop)
  (h_reflexive : reflexive rel)
  (h_transitive : transitive rel)
  (h_directed : ∀ x y, ∃ z : carrier, rel x z ∧ rel y z)


structure directed_diagram (D : (directed_type : Type (u+1))) : Type (max (u+1) (v+1)) :=
  (obj : D.carrier → Type v)
  (mor : ∀{x}, ∀{y}, D.rel x y → (obj x  → obj y))
  (h_mor : ∀{x} {y} {z} {f1 : D.rel x y} {f2 : D.rel y z} {f3 : D.rel x z},
           (mor f3) = (mor f2) ∘ (mor f1)) -- functoriality

def directed_type_of_nat : directed_type :=
  begin refine ⟨ℕ, (≤), _, _, _⟩, intro, refl,
  fapply le_trans, intros, fapply exists.intro, exact x + y,
  simp only [*, zero_le, le_add_iff_nonneg_right, and_self, le_add_iff_nonneg_left]
  end

@[simp]lemma jesse : directed_type_of_nat.carrier = ℕ := by refl

def constant_functor (D : directed_type) (A : Type v) : directed_diagram D :=
  ⟨(λ x, A), λ x y h, id, by simp⟩

def coproduct_of_directed_diagram {D : (directed_type : Type (u+1)) }
    (F : (directed_diagram D :  Type (max (u+1) (v+1)))) :  Type (max u v) :=
    Σ a : D.carrier, F.obj a

def canonical_inclusion_coproduct {D : directed_type} {F : directed_diagram D} (i : D.carrier) :
                                  F.obj i → coproduct_of_directed_diagram F := λ x, ⟨i,x⟩

def germ_relation {D : (directed_type : Type (u+1)) }
(F : (directed_diagram D :  Type (max (u+1) (v+1)))) : coproduct_of_directed_diagram F → coproduct_of_directed_diagram F  → Prop :=
λ ⟨i,x⟩ ⟨j, y⟩, ∃ k : D.carrier, ∃ z : F.obj k, ∃ f_x : D.rel i k, ∃ f_y : D.rel j k,
                 (F.mor f_x) x = z ∧ (F.mor f_y) y = z

lemma germ_equivalence {D : (directed_type : Type (u+1)) }
(F : (directed_diagram D :  Type (max (u+1) (v+1)))) : equivalence (germ_relation F) :=
begin
  split,
    {rintro ⟨i, x⟩, repeat{split}, swap, exact i, exact D.h_reflexive i},
  split,
    {intros x y, rcases x with ⟨i, x⟩, rcases y with ⟨j, y⟩, intro h,
    rcases h with ⟨ℓ,z,f_x,f_y,H⟩, repeat{fapply exists.intro},
    exacts [ℓ,z,f_y,f_x, and.intro H.right H.left]},
    {unfold transitive, intros, cases x with i x, cases y with j y, cases z with k z,
    rcases a with ⟨ℓ₁, z, fi, fj_1, Hℓ₁⟩, rcases a_1 with ⟨ℓ₂, z', fj_2, fk, Hℓ₂⟩,
    have a_2 := D.h_directed ℓ₁ ℓ₂, rcases a_2 with ⟨ℓ₃, g1, g2⟩,
    have f1 : D.rel i (ℓ₃),
      {fapply D.h_transitive, exacts [ℓ₁, fi, g1]},
    have f2 : D.rel j ℓ₃,
      {fapply D.h_transitive, exacts [ℓ₁, fj_1, g1]},
    have f3 : D.rel k (ℓ₃),
      {fapply D.h_transitive, exact ℓ₂, exact fk, exact g2},
    have H1 : F.mor f1 = F.mor g1 ∘ F.mor fi; have H2_l : F.mor f2 = F.mor g1 ∘ F.mor fj_1;
    have H2_r : F.mor f2 = F.mor g2 ∘ F.mor fj_2; have H3 : F.mor f3 = F.mor g2 ∘ F.mor fk;
    all_goals{try{fapply F.h_mor}},
    have H4 : (F.mor fi x) = (F.mor fj_1 y), by cc, dedup,
    have H5 : (F.mor fk z) = (F.mor fj_2 y), by cc,
    unfold germ_relation at *, fapply exists.intro,
    exact ℓ₃, fapply exists.intro, exact (F.mor f2) y, fapply exists.intro, exact f1,
    fapply exists.intro, exact f3, fapply and.intro,
    {simp[H1, H2_l], rw[H4]}, {simp[H2_r, H3], rw[H5]},
    }
end

def colimit {D : (directed_type : Type (u+1)) } (F : (directed_diagram D :  Type (max (u+1) (v+1)))) : Type (max u v) :=
  @quotient (coproduct_of_directed_diagram F) ⟨germ_relation F, germ_equivalence F⟩

def canonical_map {D : directed_type} {F : directed_diagram D} (i : D.carrier) :
                  F.obj i → colimit F := (by apply quotient.mk) ∘ canonical_inclusion_coproduct i

lemma canonical_map_inj_of_transition_maps_inj {D : directed_type} {F : directed_diagram D} (i : D.carrier) (H : ∀ {i} {j}, ∀ h : D.rel i j, function.injective (F.mor h)) : function.injective (@canonical_map D F i) :=
begin
    unfold function.injective canonical_map canonical_inclusion_coproduct, intros x y,
    simp only [function.comp_app, quotient.eq], simp only [(≈)], 
    unfold germ_relation, intro H_eqv, rcases H_eqv with ⟨j,z,edge,_, ⟨H1, H2⟩⟩,
    exact H edge (by cc)
end

end colimit

