import .fol tactic.tidy .abel tactic.ring .completeness

open fol

local notation h :: t  := dvector.cons h t
local notation `[]` := dvector.nil
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

namespace reflection
section

/- rephrasing of soundness -/
def by_reflection {L} (T : Theory L) {S : Structure L} [h_nonempty : nonempty S]
  {hS : S ⊨ T} (p : Prop) (ψ : sentence L) (h_p : realize_sentence S ψ ↔ p) : T ⊢' ψ → p :=
by {intro P, cases P, apply h_p.mp, apply soundness, repeat{assumption}}

open abel

/- every abelian group satisfies ∀ x ∀ y, x + (y + y) = y + (y + x) -/
def T_ab_proves_x_y_y : T_ab ⊢' ∀' ∀' (&1 +' (&0 +' &0) ≃ &0 +' (&0 +' &1)) :=
begin
  apply (completeness _ _).mpr, intros M h_nonempty hM,
  intros x y, unfold T_ab at hM, simp at hM, rcases hM with ⟨uno,dos,tres,cuatro,cinco⟩,
  have this1 := cinco x y y, have this2 := uno y x,  have this3 := uno (realize_bounded_term ([x,y]) (&0 +' &1) []) y,
  dsimp* at *,
  have : realize_bounded_term ([y, y, x]) (&2 +' (&1 +' &0)) [] = realize_bounded_term ([y, x]) (&1 +' (&0 +' &0)) [], by refl,
    rw[<-this, <-this1], 
  have : realize_bounded_term ([y, y, x]) (&2 +' &1 +' &0) [] = realize_bounded_term ([y, (realize_bounded_term ([x, y]) (&0 +' &1) [])]) (&1 +' &0) [], by refl,
    rw[this, this3, <-this2], refl
end

example : ∀ x y : ℤ, x + (y + y) = y + (y + x) :=
begin
  refine @by_reflection L_abel T_ab ℤ' (by apply_instance) (ℤ'_is_abelian_group) _ _ _ _,
  exact ∀' ∀' (&1 +' (&0 +' &0) ≃ &0 +' (&0 +' &1)), {refl}, exact T_ab_proves_x_y_y
end

example : ∀ x y : ℤ, x + (y + y) = y + (y + x) :=
by {intros, rw[add_comm,add_assoc]}

example : ∀ x y : ℤ, x + (y + y) = y + (y + x) :=
by {intros, ring}

example : ∀ x y : ℤ, x + (y + y) = y + (y + x) :=
by {simp}

example : ∀ x y : ℤ, x + (y + y) = y + (y + x) :=
by {tidy}

end
end reflection
