import .fol

open fol

local notation h :: t  := dvector.cons h t
local notation `[]` := dvector.nil
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

namespace nnf
section

/- Recurse through a formula, rewriting f ⟹ ⊥ to (∼f) when possible -/
def not_rewrite {L} : ∀{l}, preformula L l → preformula L l
| l falsum          := falsum
| l (t₁ ≃ t₂)       := t₁ ≃ t₂
| l (rel R)          := rel R
| l (apprel f t)     := apprel f t
| l (f ⟹ falsum)    := (∼f)
| l (f ⟹ g)         := (not_rewrite f) ⟹ (not_rewrite g)
| l (∀' f)           := ∀' not_rewrite f

/- Recurse through a formula, rewriting ∼(f ⟹ ∼g) to f ⊓ g -/
def and_rewrite {L} : ∀{l}, preformula L l → preformula L l
| l falsum          := falsum
| l (t₁ ≃ t₂)       := t₁ ≃ t₂
| l (rel R)          := rel R
| l (apprel f t)     := apprel f t
--| l ∼(f ⟹ (∼ g)) := f ⊓ g -- this pattern makes the equation compiler complain
| l ((f ⟹ (g ⟹ falsum)) ⟹ falsum) := f ⊓ g
| l (f ⟹ g)         := (and_rewrite f) ⟹ (and_rewrite g)
| l (∀' f)           := ∀' and_rewrite f

def or_rewrite {L} : ∀{l}, preformula L l → preformula L l
| l falsum          := falsum
| l (t₁ ≃ t₂)       := t₁ ≃ t₂
| l (rel R)          := rel R
| l (apprel f t)     := apprel f t
| l ((f ⟹ falsum) ⟹ g) := f ⊔ g
| l (f ⟹ g)         := (or_rewrite f) ⟹ (or_rewrite g)
| l (∀' f)           := ∀' or_rewrite f

def imp_rewrite {L} : ∀{l}, preformula L l → preformula L l
| l falsum          := falsum
| l (t₁ ≃ t₂)       := t₁ ≃ t₂
| l (rel R)          := rel R
| l (apprel f t)     := apprel f t
| l (f ⟹ g)         := ∼(imp_rewrite f) ⊔ (imp_rewrite g)
| l (∀' f)           := ∀' imp_rewrite f

lemma neg_rewrite_sanity_check {L} {f : formula L} : not_rewrite (f ⟹ ⊥) = (∼f) :=
  by {conv {to_lhs, rw[not_rewrite]}}

lemma and_rewrite_sanity_check {L} {f g : formula L} : and_rewrite ∼(f ⟹ (∼g)) = f ⊓ g :=
  by {conv {to_lhs, simp[fol.not], rw[and_rewrite]}}
--the simp[fol.not] is unfortunate, but the equation compiler doesn't let me use `∼` in and_rewrite

/- To put formulas into normal form,
    1. replace implication with material implication, and
    2. simplify with de-morgan's laws

    maybe hijack the simplifier?
 -/

end
end nnf
