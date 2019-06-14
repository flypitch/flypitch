import .fol .abel

universe u

-- section weekdays
-- @[derive has_reflect]
-- inductive weekday : Type
-- | monday          : weekday
-- | another_day     : weekday → weekday

-- open weekday

-- meta def dump_weekday (f : weekday) : tactic unit :=
-- tactic.trace $ to_string (expr.to_raw_fmt (reflect f).to_expr) 

-- -- run_cmd dump_weekday (another_day (another_day monday))
-- --(app (const weekday.another_day []) (app (const weekday.another_day []) (const weekday.monday [])))

-- inductive weekday' : Type
-- | monday          : weekday'
-- | another_day     : weekday' → weekday'

-- open weekday'
-- meta instance has_reflect_weekday' : has_reflect weekday'
-- | weekday'.monday                  := `(monday)
-- | (weekday'.another_day x)         := `(λ l, weekday'.another_day l).subst $
--                                         by haveI := has_reflect_weekday'; exact (reflect x)

-- meta def dump_weekday' (f : weekday') : tactic unit :=
-- tactic.trace $ to_string (expr.to_raw_fmt (reflect f).to_expr) 


-- -- run_cmd dump_weekday' (another_day (another_day monday))
-- -- (app (const weekday'.another_day []) (app (const weekday'.another_day []) (const weekday'.monday [])))
-- end weekdays
-- -- meta instance has_reflect_preterm {L : Language.{u}} : Π{n : ℕ}, has_reflect (preterm L n)
-- -- | 0 (var k) := `(@preterm.var L).subst (reflect k)

-- -- @[derive has_reflect]

-- open fol abel

-- section preterm_aux 
-- inductive preterm_aux (L : Language.{u}) : Type u
-- | var     : ℕ → preterm_aux
-- | func    : ∀ k : ℕ, L.functions k → preterm_aux
-- | app     : preterm_aux → preterm_aux → preterm_aux

-- def to_aux {L : Language.{u}} : ∀ {l : ℕ},  preterm L l → preterm_aux L
-- | 0 (var n)      := preterm_aux.var _ n
-- | k (func f)     := preterm_aux.func _ f
-- | k (app t₁ t₂)  := preterm_aux.app (to_aux t₁) (to_aux t₂)


-- def L_abel_plus' (t₁ t₂ : preterm L_abel 0) : preterm L_abel 0 :=
-- @term_of_function L_abel 2 (abel_functions.plus : L_abel.functions 2) t₁ t₂
-- end preterm_aux

-- local infix ` +' `:100 := L_abel_plus'

-- local notation ` zero ` := (func abel_functions.zero : preterm L_abel 0)

-- section L_abel_term_biopsy

-- def sample1 : preterm L_abel 0 := (zero +' zero)

-- def sample2 : preterm L_abel 0 := zero

-- -- #reduce sample2

-- open expr
-- meta def sample2_expr : expr :=
-- mk_app (const `preterm.func list.nil) ([(const `L_abel list.nil), `(0), const `abel_functions.zero list.nil] : list expr)

-- end L_abel_term_biopsy

-- section simpler_biopsy

-- inductive my_inductive : Type
-- | a : my_inductive
-- | b : my_inductive
-- | f : my_inductive → my_inductive

-- open my_inductive
-- def sample3 : my_inductive := f a

-- open expr

-- meta def sample3_expr : expr :=
-- app (const `my_inductive.f list.nil) (const `my_inductive.a list.nil)

-- def sample3_again : my_inductive := by tactic.exact (sample3_expr)

-- example : sample3 = sample3_again := rfl

-- end simpler_biopsy

-- namespace tactic
-- namespace interactive
-- open interactive interactive.types expr

-- def my_test_term : preterm L_abel 0 := (zero +' zero)

-- end interactive
-- end tactic

-- section test
-- -- def my_term : preterm L_abel 0 := sorry

-- -- #check tactic.interactive.rcases

-- end test

-- section sample4

-- /-- Note: this is the same as `dfin` -/
-- inductive my_indexed_family : ℕ → Type u
-- | z {} : my_indexed_family 0
-- | s : ∀ {k}, my_indexed_family k → my_indexed_family (k+1)

-- -- meta example : ∀ {n}, has_reflect (my_indexed_family n)
-- -- | 0 z := `(z)


-- open my_indexed_family

-- def sample4 : my_indexed_family 1 := s z

-- -- #check tactic.eval_expr

-- end sample4

-- section sample4

-- inductive dfin'' : ℕ → Type
-- | fz {n} : dfin'' (n+1)
-- | fs {n} : dfin'' n → dfin'' (n+1)

-- inductive dfin' : ℕ → Type u
-- | gz {n} :  dfin' (n+1)
-- | gs {n} :  dfin' n → dfin' (n+1)

-- open dfin dfin'

-- meta instance dfin.reflect : ∀ {n}, has_reflect (dfin'' n)
-- | _ dfin''.fz := `(dfin''.fz)
-- | _ (dfin''.fs n) := `(dfin''.fs).subst (dfin.reflect n)

-- -- /- errors all over---why doesn't reflect like universe parameters? -/
-- -- meta instance dfin'.reflect : ∀ {n}, has_reflect (dfin' n)
-- -- | _ fz := `(fz)
-- -- | _ (fs n) := `(fs).subst (dfin'.reflect n)

-- end sample4

-- section reflect_preterm

-- /- Language with a single constant symbol -/
-- inductive L_pt_functions : ℕ → Type
-- | pt : L_pt_functions 0

-- def L_pt : Language.{0} := ⟨L_pt_functions, λ _, empty⟩

-- def pt_preterm : preterm L_pt 0 := preterm.func L_pt_functions.pt

-- meta def pt_preterm_reflected : expr :=
-- expr.mk_app (expr.const `preterm.func [level.zero]) [ (expr.const `L_pt list.nil), `(0), (expr.const `L_pt_functions.pt list.nil)]

-- set_option trace.app_builder true

-- -- meta def pt_preterm_reflected' : expr := by tactic.mk_app "preterm.func" [(expr.const `L_pt []), `(0), (expr.const `L_pt_functions.pt [])]

-- #check tactic.mk_app

-- meta def pt_preterm_reflected'' : tactic expr :=
-- tactic.to_expr ```(preterm.func L_pt_functions.pt : preterm L_pt 0)

-- def pt_preterm' : preterm L_pt 0 := by pt_preterm_reflected'' >>= tactic.exact

-- -- def pt_preterm' : preterm L_pt 0 := by tactic.exact pt_preterm_reflected

-- example : pt_preterm = pt_preterm' := rfl
--   -- infer type failed, incorrect number of universe levels

-- -- want: example : pt_preterm = pt_preterm' := rfl


-- end reflect_preterm


-- namespace hewwo
-- section reflect_preterm2
-- def L_pt.pt' : L_pt.functions 0 := L_pt_functions.pt

-- #reduce (by apply_instance : reflected L_pt.pt')
-- -- `(L_pt.pt')

-- meta def pt_preterm_reflected : tactic expr :=
-- tactic.mk_app ``preterm.func [`(L_pt.pt')]

-- def pt_preterm' : preterm L_pt 0 := by pt_preterm_reflected >>= tactic.exact

-- #eval tactic.trace (@expr.to_raw_fmt tt `(L_pt.pt'))

-- #check reflect


-- end reflect_preterm2
-- end hewwo

-- section reflect_preterm3

-- inductive L_pt_func_functions : ℕ → Type
-- | pt  : L_pt_func_functions 0
-- | foo : L_pt_func_functions 1

-- open L_pt_func_functions

-- def L_pt_func : Language.{0} :=
-- ⟨L_pt_func_functions, λ _, ulift empty⟩

-- -- def foo_pt_term : preterm L_pt_func 0 :=
-- -- preterm.app (preterm.func L_pt_func_functions.foo) (preterm.func L_pt_func_functions.pt)

-- -- def foo_pt_term_reflected : expr :=
-- -- begin
-- --   tactic.mk_app ``preterm.func [(by tactic.mk_app `preterm.func [`(L_pt_func_functions.foo)]), (by tactic.mk_app `preterm.func [`(L_pt_func_functions.pt)])]
-- -- end

-- -- def foo' : preterm L_pt_func 1 := preterm.func L_pt_func_functions.foo


-- -- #reduce (by apply_instance : reflected L_pt_func_functions.foo)

-- set_option trace.app_builder true

-- def my_foo : L_pt_func.functions 1 := L_pt_func_functions.foo

-- def my_pt : L_pt_func.functions 0 := L_pt_func_functions.pt

-- -- meta def foo_pt_term_reflected : tactic expr := tactic.mk_app ``preterm.func [`()]

-- meta def foo_pt_term_reflected' : tactic expr :=
-- do e₁ <- tactic.mk_app ``preterm.func [`(my_foo)],
--    e₂ <- tactic.mk_app ``preterm.func [`(my_pt)],
--    tactic.mk_app ``preterm.app [e₁, e₂]
-- -- #print foo_pt_term_reflected'



-- -- meta def bar : tactic expr :=
-- --   tactic.mk_app ``preterm.func [`(foo_mask)]

-- set_option trace.app_builder true

-- def foo_pt_term_reflected : preterm L_pt_func 0 := by (foo_pt_term_reflected' >>= tactic.exact)

-- -- #reduce foo_pt_term_reflected


-- end reflect_preterm3
