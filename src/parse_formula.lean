import .abel .fol

universe u

@[derive has_reflect]
inductive fmla
| var : nat → fmla
| pi : fmla → fmla

meta def to_fmla : pexpr → option fmla
| (expr.var n) := some (fmla.var n)
| (expr.pi _ _ _ e) := fmla.pi <$> to_fmla e
| _ := none

namespace tactic
namespace interactive
open interactive interactive.types expr

meta def parse_formula (e : parse texpr) : tactic unit :=
do f <- to_fmla e, tactic.exact `(f)

end interactive
end tactic

def foo : fmla := by parse_formula (∀ x : ℕ, x)
#print foo -- fmla.pi (fmla.var 0)

-- meta def my_dumb_reflect (n : ℕ) : tactic unit :=
-- tactic.exact (reflect (n+1))

-- meta def my_dumber_reflect (n : ℕ) : tactic unit :=
-- tactic.trace `n

-- meta def my_dumber_reflect' (x : ℕ) : tactic unit :=
-- tactic.to_expr ```(n + 1) >>= tactic.exact
-- run_cmd my_dumber_reflect 500 -- n

-- def foo' : ℕ := by my_dumber_reflect 500



-- meta def my_dumber_reflect' (x : ℕ) : tactic unit :=
-- tactic.exact `(n + 1)

meta def foo' : expr := `(0 + 0)

run_cmd tactic.trace ((expr.to_raw_fmt foo'))

open abel fol

section abel_parse_formula

#print preterm

#print expr

meta def to_term : Π {n : ℕ}, pexpr → option (preterm L_abel n)
| 0     (expr.var k)                  := some (var k)
| 0     (expr.const `has_zero.zero _) := some (func abel_functions.zero)
| 2     (expr.const `has_add.add _)   := some (func abel_functions.plus)
| (k) (expr.app e₁ e₂)                := do t₁ <- to_term e₁,
                                            t₂ <- to_term e₂,
                                            return (app t₁ t₂)
| _ _                                 := none

-- meta def to_term {n} : pexpr → option (preterm L_abel n)
-- | (expr.var k)                  := (some (var k) : preterm L_abel 0)
-- | (expr.const `has_add.add _)   := some (func abel_functions.plus)
-- | (expr.app e₁ e₂)              := some (


end abel_parse_formula

@[derive has_reflect]
inductive weekday : Type
| monday          : weekday
| another_day     : weekday → weekday

export weekday

meta def dump_weekday (f : weekday) : tactic unit :=
tactic.trace $ to_string (expr.to_raw_fmt (reflect f).to_expr) 

run_cmd dump_weekday (another_day (another_day monday))
--(app (const weekday.another_day []) (app (const weekday.another_day []) (const weekday.monday [])))

inductive weekday' : Type
| monday          : weekday'
| another_day     : weekday' → weekday'

export weekday'
meta instance has_reflect_weekday' : has_reflect weekday'
| weekday'.monday                  := `(monday)
| (weekday'.another_day x)         := `(λ l, weekday'.another_day l).subst $
                                        by haveI := has_reflect_weekday'; exact (reflect x)

meta def dump_weekday' (f : weekday') : tactic unit :=
tactic.trace $ to_string (expr.to_raw_fmt (reflect f).to_expr) 


run_cmd dump_weekday' (another_day (another_day monday))
-- (app (const weekday'.another_day []) (app (const weekday'.another_day []) (const weekday'.monday [])))

-- meta instance has_reflect_preterm {L : Language.{u}} : Π{n : ℕ}, has_reflect (preterm L n)
-- | 0 (var k) := `(λ y, preterm.var y).subst `(reflect k)


def L_abel_plus' (t₁ t₂ : preterm L_abel 0) : preterm L_abel 0 :=
@term_of_function L_abel 2 (abel_functions.plus : L_abel.functions 2) t₁ t₂

local infix ` +' `:100 := L_abel_plus'

local notation ` zero ` := (func abel_functions.zero : preterm L_abel 0)
meta def str_preterm : ∀ n : ℕ, ℕ → preterm L_abel n → string
 | n z &k := "x" ++ to_string(z - k)
 | n z (func abel_functions.zero) := "0"
 | n z (func abel_functions.plus) := "+"
 | n z (app t₁ t₂) := (str_preterm _ z t₁) ++ "(" ++ (str_preterm _ z  t₂) ++ ")"

#eval str_preterm _ 4 (zero +' zero)

namespace tactic
namespace interactive
open interactive interactive.types expr

#check format

def my_test_term : preterm L_abel 0 := (zero +' zero)

@[instance]meta def format_preterm {n} : has_to_tactic_format (preterm L_abel n) :=
{ to_tactic_format := λ t, return ((str_preterm _ 0 t)) }

meta def parse_term (n : ℕ) (e : parse texpr) : tactic unit :=
do trace "hello"

example : false :=
begin
  parse_term 0 (&0 : preterm L_abel 0)
end

-- def my_dumb_term : preterm L_abel 0 := by parse_term 0 (abel_functions.zero)

end interactive
end tactic

section test
def my_term : preterm L_abel 0 := sorry

#check tactic.interactive.rcases

end test
