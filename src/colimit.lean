import .fol order tactic.tidy .to_mathlib

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

def directed_type_of_nat : directed_type :=
  begin refine ⟨ℕ, (≤), _⟩,
  intros x y, fapply exists.intro, exact x + y,
  simp only [*, zero_le, le_add_iff_nonneg_right, and_self, le_add_iff_nonneg_left]
  end

def constant_functor (D : directed_type) (A : Type v) : directed_diagram D :=
  ⟨(λ x, A), λ x y h, id⟩

def coproduct_of_directed_diagram {D : (directed_type : Type (u+1)) }
    (F : (directed_diagram D :  Type (max (u+1) (v+1)))) :  Type (max u v) :=
    Σ a : D.carrier, F.obj a

def germ_relation {D : (directed_type : Type (u+1)) }
(F : (directed_diagram D :  Type (max (u+1) (v+1)))) : coproduct_of_directed_diagram F → coproduct_of_directed_diagram F  → Prop :=
λ ⟨i,x⟩ ⟨j, y⟩, ∃ k : D.carrier, ∃ z : F.obj k, ∃ f_x : D.rel i k, ∃ f_y : D.rel j k,
                 (F.mor f_x) x = z ∧ (F.mor f_y) y = z

example (A B : Type) (f : A → B) (a_1 a_2 : A) : a_1 = a_2 → f a_1 = f a_2 :=
  by {intro, simp only [*, eq_self_iff_true]}

lemma germ_equivalence {D : (directed_type : Type (u+1)) }
(F : (directed_diagram D :  Type (max (u+1) (v+1)))) : equivalence (germ_relation F) :=
begin
  split,
    {rintro ⟨i, x⟩, repeat{split}, swap, exact i, exact D.h_reflexive i},
  split,
    {sorry},
    {unfold transitive, intros, cases x with i x, cases y with j y, cases z with k z,
    have ℓ₁ := psigma_of_exists a, have ℓ₂ := psigma_of_exists a_1,
    have a2 := psigma_of_exists (D.h_directed ℓ₁.fst ℓ₂.fst),
    have f1 : D.rel i (a2.fst),
      {fapply D.h_transitive, exact ℓ₁.fst, cases ℓ₁.snd, exact h.fst, exact a2.snd.left},
    have f2 : D.rel j a2.fst,
      {fapply D.h_transitive, exact ℓ₁.fst, cases ℓ₁.snd, exact h.snd.fst, exact a2.snd.left},
    have f3 : D.rel k (a2.fst),
      {fapply D.h_transitive, exact ℓ₂.fst, cases ℓ₂.snd, exact h.snd.fst, exact a2.snd.right},
    have fi : D.rel i ℓ₁.fst, by {cases ℓ₁.snd, exact h.fst},
    have fj_1 : D.rel j ℓ₁.fst, by {cases ℓ₁.snd, exact h.snd.fst},
    have fj_2 : D.rel j ℓ₂.fst, by {cases ℓ₂.snd, exact h.fst},
    have fk : D.rel k ℓ₂.fst, by {cases ℓ₂.snd, exact h.snd.fst},
    have g1 : D.rel ℓ₁.fst a2.fst, by {exact a2.snd.left},
    have g2 : D.rel ℓ₂.fst a2.fst, by {exact a2.snd.right},
    have H1 : ∀ x, F.mor f1 x = F.mor g1 (F.mor fi x),
      {sorry},
    have H2_l : ∀ y, F.mor f2 y = F.mor g1 (F.mor fj_1 y),
      {sorry},
    have H2_r : ∀ y, F.mor f2 y = F.mor g2 (F.mor fj_2 y),
      {sorry},
    have H3 : ∀ z, F.mor f3 z = F.mor g2 (F.mor fk z),
      {sorry},
    
    unfold germ_relation at *, fapply exists.intro,
    exact a2.fst, fapply exists.intro, exact (F.mor f2) y, fapply exists.intro, exact f1,
    fapply exists.intro, exact f3, split,
    {simp[H1, H2_l], sorry},
    {simp[H2_r, H3], sorry},
    }
end

def colimit {D : (directed_type : Type (u+1)) } (F : (directed_diagram D :  Type (max (u+1) (v+1)))) : Type (max u v) :=
begin
  fapply quotient, exact coproduct_of_directed_diagram F,
  exact ⟨germ_relation F, germ_equivalence F⟩
end

end colimit
