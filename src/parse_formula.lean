/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s):

Parsing formulas from Lean expressions.
-/

import .abel .fol tactic data.list

universe u

/- toy example by Mario -/
section fmla
@[derive has_reflect]
inductive fmla
| var : nat → fmla
| pi : fmla → fmla

meta def to_fmla : pexpr → option fmla
| (expr.var n) := some (fmla.var n)
| (expr.pi _ _ _ e) := fmla.pi <$> to_fmla e
| _ := none

end fmla

namespace tactic
namespace interactive

section parse_fmla
open interactive interactive.types expr

meta def parse_fmla (e : parse texpr) : tactic unit :=
do f <- to_fmla e, tactic.exact `(f)

end parse_fmla
end interactive
end tactic

def foo : fmla := by parse_fmla (∀ x : ℕ, x)
-- #print foo -- fmla.pi (fmla.var 0)
/- end toy example -/

open fol
meta instance preterm.reflect {L : Language.{0}} [reflected L] [∀ n, has_reflect (L.functions n)] :
  ∀{n}, has_reflect (preterm L n)
| _ &k          := `(&k)
| _ (func f)    := `(func f)
| _ (app t₁ t₂) := (`(λ x y, app x y).subst (preterm.reflect t₁)).subst (preterm.reflect t₂)

meta instance preformula.reflect {L : Language.{0}} [reflected L] [∀ n, has_reflect (L.functions n)]
  [∀ n, has_reflect (L.relations n)] : ∀{n}, has_reflect (preformula L n)
| _ falsum           := `(falsum)
| _ (equal t₁ t₂)    := (`(λ x₁ x₂, equal x₁ x₂).subst (preterm.reflect t₁)).subst (preterm.reflect t₂)
| _ (rel R)          := `(λ x, preformula.rel x).subst `(R)
| _ (apprel f t)     := (`(λ x₁ x₂, apprel x₁ x₂).subst (preformula.reflect f)).subst (preterm.reflect t)
| _ (imp f₁ f₂)      := (`(λ x₁ x₂, imp x₁ x₂).subst (preformula.reflect f₁)).subst (preformula.reflect f₂)
| _ (all f)          := `(λ x, all x).subst (preformula.reflect f)


meta instance L_empty.reflect : reflected L_empty := by apply_instance
meta instance L_empty_functions_reflect : ∀ n, has_reflect (L_empty.functions n) :=
λ _ _, empty.elim ‹_›

meta instance L_empty_relations_reflect : ∀ n, has_reflect (L_empty.relations n) :=
λ _ _, empty.elim ‹_›

section L_empty_parse

meta def to_term_empty : Π {n : ℕ}, expr → option (preterm L_empty n)
| 0     (expr.var k)    := some (var k)
| _     _               := none

-- TODO() insert a case analysis on whether e' : Prop to determine whether or not to use imp
meta def to_formula_empty : Π {n : ℕ}, expr → option (preformula L_empty n)
| 0 (expr.pi _ _ e' e)     := ((to_formula_empty e) >>= (λ f, return (all f)))
| 0 `(%%a = %%b)          := do e₁ <- to_term_empty a, e₂ <- to_term_empty b,
                               return $ equal e₁ e₂
-- | 0 `(%%a → %%b)          := do e₁ <- to_formula_empty a, e₂ <- to_formula_empty b,
--                                return $ imp e₁ e₂ -- equation compiler thinks this case
                                   -- is redundant since a → b compiles to Π _ : a, b
| 0 `(false)              := return (falsum)
| 0  _                    := none
| (n+1) _                 := none

end L_empty_parse
namespace tactic
namespace interactive

open interactive interactive.types expr
meta def parse_formula (t : parse texpr) : tactic unit := 
  do f <- ((@to_formula_empty 0) <$> (to_expr t)),
     match f with
     | (some ϕ) := tactic.exact `(ϕ)
     | none     := tactic.fail "to_formula_empty failed to parse"
     end



end interactive
end tactic

-- meta def test : expr := `(true → true)

-- meta def test' : expr := `(∀ x : ℕ, x = 0)

-- #eval (@expr.to_raw_fmt tt test).to_string

-- #eval (@expr.to_raw_fmt tt test').to_string

constant α : Type

def my_little_formula : preformula L_empty 0 :=
by parse_formula (∀ x : α, x = x)

def my_larger_formula : preformula L_empty 0 :=
by parse_formula (∀ x y : α, (x = y))

-- #reduce my_little_formula -- it works!
-- ∀'(&0 ≃ &0)

-- #print my_larger_formula -- it still works!
-- ∀'∀'(&1 ≃ &0)

