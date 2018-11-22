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

lemma germ_equivalence {D : (directed_type : Type (u+1)) }
(F : (directed_diagram D :  Type (max (u+1) (v+1)))) : equivalence (germ_relation F) :=
begin
  split,
    {rintro ⟨i, x⟩, repeat{split}, swap, exact i, exact D.h_reflexive i},
  split,
    {sorry}, -- this is just tidy, but i'll optimize later
    {unfold transitive, intros, cases x with i x, cases y with j y, cases z with k z,
    have a_w := psigma_of_exists a, have a_1_w := psigma_of_exists a_1,
    have a2 := psigma_of_exists (D.h_directed a_w.fst a_1_w.fst),
    unfold germ_relation at *, repeat{fapply exists.intro},
    exact a2.fst,
    repeat{sorry} -- rest of this should be easy but i'm sleepy
    }
end

def colimit {D : (directed_type : Type (u+1)) } (F : (directed_diagram D :  Type (max (u+1) (v+1)))) : Type (max u v) :=
begin
  fapply quotient, exact coproduct_of_directed_diagram F,
  exact ⟨germ_relation F, germ_equivalence F⟩
end

end colimit
