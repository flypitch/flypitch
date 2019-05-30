import .abel .fol tactic

/-
namespace expr
open format
private meta def p := λ xs, paren (format.join (list.intersperse " " xs))

meta def to_raw_fmt' {elab : bool} : expr elab → format
| (var n) := p ["var", _root_.to_string n]
| (sort l) := p ["sort", _root_.to_string l]
| (const n ls) := p ["const", _root_.to_string n, _root_.to_string ls]
| (mvar n m t)   := p ["mvar", _root_.to_string n, _root_.to_string m, to_raw_fmt t]
| (local_const n m bi t) := p ["local_const", _root_.to_string n, _root_.to_string m, to_raw_fmt t]
| (app e f) := p ["app", to_raw_fmt e, to_raw_fmt f]
| (lam n bi e t) := p ["lam", _root_.to_string n, repr bi, to_raw_fmt e, to_raw_fmt t]
| (pi n bi e t) := p ["pi", _root_.to_string n, repr bi, to_raw_fmt e, to_raw_fmt t]
| (elet n g e f) := p ["elet", _root_.to_string n, to_raw_fmt g, to_raw_fmt e, to_raw_fmt f]
| (macro d args) := sbracket (format.join (list.intersperse " " ("macro" :: _root_.to_string (macro_def_name d) :: args.map to_raw_fmt)))

end expr
-/

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

section parse_formula
open interactive interactive.types expr

meta def parse_formula (e : parse texpr) : tactic unit :=
do f <- to_fmla e, tactic.exact `(f)

end parse_formula
end interactive
end tactic

def foo : fmla := by parse_formula (∀ x : ℕ, x)
-- #print foo -- fmla.pi (fmla.var 0)

meta def my_dumb_reflect (n : ℕ) : tactic unit :=
tactic.exact (reflect (n+1))

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

section weekdays
@[derive has_reflect]
inductive weekday : Type
| monday          : weekday
| another_day     : weekday → weekday

open weekday

meta def dump_weekday (f : weekday) : tactic unit :=
tactic.trace $ to_string (expr.to_raw_fmt (reflect f).to_expr) 

run_cmd dump_weekday (another_day (another_day monday))
--(app (const weekday.another_day []) (app (const weekday.another_day []) (const weekday.monday [])))

inductive weekday' : Type
| monday          : weekday'
| another_day     : weekday' → weekday'

open weekday'
meta instance has_reflect_weekday' : has_reflect weekday'
| weekday'.monday                  := `(monday)
| (weekday'.another_day x)         := `(λ l, weekday'.another_day l).subst $
                                        by haveI := has_reflect_weekday'; exact (reflect x)

meta def dump_weekday' (f : weekday') : tactic unit :=
tactic.trace $ to_string (expr.to_raw_fmt (reflect f).to_expr) 


run_cmd dump_weekday' (another_day (another_day monday))
-- (app (const weekday'.another_day []) (app (const weekday'.another_day []) (const weekday'.monday [])))
end weekdays
-- meta instance has_reflect_preterm {L : Language.{u}} : Π{n : ℕ}, has_reflect (preterm L n)
-- | 0 (var k) := `(λ y, preterm.var y).subst begin end

-- @[derive has_reflect]

section preterm_aux 
inductive preterm_aux (L : Language.{u}) : Type u
| var     : ℕ → preterm_aux
| func    : ∀ k : ℕ, L.functions k → preterm_aux
| app     : preterm_aux → preterm_aux → preterm_aux

def to_aux {L : Language.{u}} : ∀ {l : ℕ},  preterm L l → preterm_aux L
| 0 (var n)      := preterm_aux.var _ n
| k (func f)     := preterm_aux.func _ f
| k (app t₁ t₂)  := preterm_aux.app (to_aux t₁) (to_aux t₂)


def L_abel_plus' (t₁ t₂ : preterm L_abel 0) : preterm L_abel 0 :=
@term_of_function L_abel 2 (abel_functions.plus : L_abel.functions 2) t₁ t₂
end preterm_aux

local infix ` +' `:100 := L_abel_plus'

local notation ` zero ` := (func abel_functions.zero : preterm L_abel 0)

section L_abel_term_biopsy

def sample1 : preterm L_abel 0 := (zero +' zero)

def sample2 : preterm L_abel 0 := zero

-- #reduce sample2

open expr
meta def sample2_expr : expr :=
mk_app (const `preterm.func list.nil) ([(const `L_abel list.nil), `(0), const `abel_functions.zero list.nil] : list expr)

-- begin
--   refine app _ _,
--   exact const `preterm.func list.nil,
--   exact const `abel_functions.zero list.nil
-- end

-- #check mk_app

-- #print preterm.func

-- #eval (to_raw_fmt sample2_expr).to_string

-- def sample2_again : preterm L_abel 0 :=
-- by tactic.exact sample2_expr -- unknown declaration preterm.func

end L_abel_term_biopsy

section simpler_biopsy

inductive my_inductive : Type
| a : my_inductive
| b : my_inductive
| f : my_inductive → my_inductive

open my_inductive
def sample3 : my_inductive := f a

open expr

meta def sample3_expr : expr :=
app (const `my_inductive.f list.nil) (const `my_inductive.a list.nil)

def sample3_again : my_inductive := by tactic.exact (sample3_expr)

example : sample3 = sample3_again := rfl

end simpler_biopsy


 
-- meta def str_preterm : ∀ n : ℕ, ℕ → preterm L_abel n → string
--  | n z &k := "x" ++ to_string(z - k)
--  | n z (func abel_functions.zero) := "0"
--  | n z (func abel_functions.plus) := "+"
--  | n z (app t₁ t₂) := (str_preterm _ z t₁) ++ "(" ++ (str_preterm _ z  t₂) ++ ")"

-- #eval str_preterm _ 4 (zero +' zero)

namespace tactic
namespace interactive
open interactive interactive.types expr

def my_test_term : preterm L_abel 0 := (zero +' zero)

-- @[instance]meta def format_preterm {n} : has_to_tactic_format (preterm L_abel n) :=
-- { to_tactic_format := λ t, return ((str_preterm _ 0 t)) }

meta def parse_term -- (n : ℕ) (e : parse texpr)
: tactic unit :=
do trace "hello"

-- example : false :=
-- begin
--   parse_term, sorry
-- end

-- def my_dumb_term : preterm L_abel 0 := by parse_term 0 (abel_functions.zero)

end interactive
end tactic

section test
-- def my_term : preterm L_abel 0 := sorry

-- #check tactic.interactive.rcases

end test


section sample4

/-- Note: this is the same as `dfin` -/
inductive my_indexed_family : ℕ → Type u
| z {} : my_indexed_family 0
| s : ∀ {k}, my_indexed_family k → my_indexed_family (k+1)

open my_indexed_family

def sample4 : my_indexed_family 1 := s z

-- #check tactic.eval_expr

end sample4
