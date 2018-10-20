import .language_term_n2

open fol

section zfc

inductive ZFC_rel
| ϵ

def L_ZFC : Language := 
begin
split,
{ intro arityf,
exact empty},
{intro arityr,
exact if arityr = 2 then ZFC_rel else empty},
end

#print L_ZFC -- good


inductive ZFC'_f0 : Type
| emptyset

inductive ZFC'_f1 : Type
| union
| pow

inductive ZFC'_f2 : Type
| pair

inductive ZFC'_rel : Type
| ϵ
| subset 

def L_ZFC' : Language :=
begin
split,
{intro arityf,
exact if arityf = 0
      then ZFC'_f0
      else (if arityf = 1
           then ZFC'_f1
           else (if arityf = 2
                then ZFC'_f2
                else empty))   },
{
{intro arityr,
exact if arityr = 2 then ZFC'_rel else empty},
}
end

-- is there a way to do this with the equation compiler instead?

lemma duh : L_ZFC'.relations 2 = ZFC'_rel :=
by refl

@[reducible]def rel_is_rel : ZFC'_rel → L_ZFC'.relations 2 :=
begin
intro,
simp[duh],
assumption
end

/- state the ZFC axioms using L_ZFC' and prove that they are sentences -/

-- for reference:
-- notation `⊥` := _root_.fol.preformula.falsum -- input: \bot
-- infix ` ≃ `:88 := _root_.fol.preformula.equal -- input \~- or \simeq
-- infix ` ⟹ `:62 := _root_.fol.preformula.imp -- input \==>
-- prefix `∼`:max := _root_.fol.not -- input \~, the ASCII character ~ has too low precedence
-- infixr ` ⊔ ` := _root_.fol.or -- input: \sqcup
-- infixr ` ⊓ ` := _root_.fol.and -- input: \sqcap
-- prefix `∀'`:110 := _root_.fol.preformula.all
-- prefix `∃'`:110 := _root_.fol.ex
--set_option pp.notation true

-- def b_not {L : Language} (n : ℕ) (f : preformula L 0) (hf : formula_below n f)  : formula_below n (fol.not f) := begin
-- simp[fol.not],
-- refine formula_below.b_imp _ _ _ _,
-- assumption,
-- exact formula_below.b_falsum
-- end

-- def b_and {L : Language} (n : ℕ) (f g : preformula L 0) (hf : formula_below n f) (hg : formula_below n g) : formula_below n (fol.and f g) :=
-- begin
-- simp[fol.and],
-- refine b_not _ _ _,
-- refine formula_below.b_imp _ _ _ _,
-- assumption,
-- apply b_not,
-- assumption
-- end

-- def b_biimp {L : Language} (n : ℕ) (f g : preformula L 0) (hf : formula_below n f) (hg : formula_below n g) : formula_below n (f ⟺ g) :=
-- begin
-- simp[biimp,fol.and, fol.not],
-- refine formula_below.b_imp _ _ _ _,
-- have := formula_below.b_falsum, -- can we add this to _every_ local context?
-- refine formula_below.b_imp _ _ _ _,
-- refine formula_below.b_imp _ _ _ _,
-- assumption, assumption,
-- refine formula_below.b_imp _ _ _ _,
-- refine formula_below.b_imp _ _ _ _,
-- assumption, assumption, assumption,
-- have := formula_below.b_falsum,
-- assumption
-- end


def axiom_of_emptyset : @sentence L_ZFC' := -- for all x, x is not in the constant emptyset.
begin
split, swap,
  {
  dsimp[formula],
  {exact (∀'∼(apprel (apprel (rel ZFC'_rel.ϵ) &0) (func ZFC'_f0.emptyset)))},},

{ simp*,
  refine b_all _ _,
  refine b_not _ _ _,
  refine b_apprel _ _ _ _,
  refine b_apprel _ _ _ _,
  refine b_rel _,
  refine term_below.b_var _ _,
  simp*,
  apply nat.zero_lt_succ,
  refine term_below.b_func _ }
end

def axiom_of_subset : @sentence L_ZFC' := -- for all x, for all z, x ⊆ y (if and only if) , z ∈ x → z ∈ y.
begin
split,
swap,
  {
  dsimp[formula],
  {exact ∀' (∀'( ∀'( (apprel (apprel (rel $ rel_is_rel ZFC'_rel.subset) &0) (var 2)) ⟺ (apprel (apprel (rel ZFC'_rel.ϵ) &1) (var 2)))))}},
{
simp*,
refine b_all _ _,
refine b_all _ _,
refine b_all _ _,
refine b_biimp _ _ _ _ _,
refine b_apprel _ _ _ _,
refine b_apprel _ _ _ _,
{refine b_rel _},
{simp*, refine term_below.b_var _ _, apply nat.zero_lt_succ},
{simp*, refine term_below.b_var _ _, simp*, apply nat.zero_lt_succ},
{refine b_apprel _ _ _ _, 
{refine b_apprel _ _ _ _,
refine b_rel _,
{simp*, refine term_below.b_var _ _, simp*, apply nat.zero_lt_succ}
},
{{simp*, refine term_below.b_var _ _, simp*, apply nat.zero_lt_succ}}
}}
end

/- less efficient proof below -/
--   {simp*,
-- have : @formula_below L_ZFC' 0 1 (fol.not (apprel (apprel (rel ZFC_rel.ϵ) &0) (func ZFC'_f0.emptyset))),
--      {
--      have : @formula_below L_ZFC' 0 1 (apprel (apprel (rel ZFC_rel.ϵ) &0) (func ZFC'_f0.emptyset)), 
--      {
--     refine formula_below.b_apprel _ _ _ _,
--  swap,
-- refine term_below.b_func _,
-- refine formula_below.b_apprel _ _ _ _,
-- refine formula_below.b_rel _,
-- refine term_below.b_var _ _,
--  apply nat.zero_lt_succ
-- }
-- ,
-- refine b_not _ _ _,
-- exact this
--        },
--        exact (s_all (fol.not (apprel (apprel (rel $ rel_is_rel ZFC_rel.ϵ) &0) (func ZFC'_f0.emptyset))) this).snd}


def axiom_of_extensionality : @sentence L_ZFC' := -- for all x for all y for all z, z in x iff z in y implies x = y
begin
split,
{sorry},
{
simp[formula],
{exact sorry}
}
end



-- etc

inductive ZFC' : (@sentence L_ZFC') → Prop -- should this be Type-valued instead?
:= sorry

end zfc

