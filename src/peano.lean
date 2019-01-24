import .fol tactic.tidy tactic.linarith .realization

-- local attribute [instance, priority 0] classical.prop_decidable
--local attribute [instance] classical.prop_decidable

local notation h :: t  := dvector.cons h t
local notation `[]` := dvector.nil
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

namespace peano

open fol
section PA

/- The language of PA -/
inductive peano_functions : ℕ → Type -- thanks Floris!
| zero : peano_functions 0
| succ : peano_functions 1
| plus : peano_functions 2
| mult : peano_functions 2

def L_peano : Language := ⟨peano_functions, λ n, empty⟩

def L_peano_plus {n} (t₁ t₂ : bounded_term L_peano n) : bounded_term L_peano n := 
@bounded_term_of_function L_peano 2 n peano_functions.plus t₁ t₂
def L_peano_mult {n} (t₁ t₂ : bounded_term L_peano n) : bounded_term L_peano n := 
@bounded_term_of_function L_peano 2 n peano_functions.mult t₁ t₂

local infix ` +' `:100 := L_peano_plus
local infix ` ×' `:150 := L_peano_mult

def succ {n} : bounded_term L_peano n → bounded_term L_peano n := 
@bounded_term_of_function L_peano 1 n peano_functions.succ
def zero {n} : bounded_term L_peano n := bd_const peano_functions.zero
def one {n} : bounded_term L_peano n := succ zero

/- For each k : ℕ, return the bounded_term of L_peano corresponding to k-/
@[reducible]def formal_nat {n}: Π k : ℕ, bounded_term L_peano n
| 0 := zero
| (k+1) := succ $ formal_nat k

/- for all x, zero not equal to succ x -/
def p_zero_not_succ : sentence L_peano :=
∀'(zero ≃ succ &0 ⟹ ⊥)

@[reducible]def shallow_zero_not_succ : Prop :=
∀ n : ℕ, 0 = nat.succ n → false

def p_succ_inj : sentence L_peano := ∀' ∀'(succ &1 ≃ succ &0 ⟹ &1 ≃ &0)

@[reducible]def shallow_succ_inj : Prop := ∀ x, ∀ y, nat.succ x = nat.succ y → x = y

def p_zero_is_identity : sentence L_peano := ∀'(&0 +' zero ≃ &0)

@[reducible]def shallow_zero_is_identity : Prop := ∀ x : ℕ, x + 0 = x

/- ∀ x ∀ y,  x + succ y = succ( x + y) -/
def p_succ_plus : sentence L_peano := ∀' ∀'(&1 +' succ &0 ≃ succ (&1 +' &0))

@[reducible]def shallow_succ_plus : Prop := ∀ x, ∀ y, x + nat.succ y = nat.succ(x + y)

/- ∀ x, x ⬝ 0 = 0 -/
def p_zero_of_times_zero : sentence L_peano := ∀'(&0 ×' zero ≃ zero)

@[reducible]def shallow_zero_of_times_zero : Prop := ∀ x : ℕ, x * 0 = 0 

/- ∀ x y, (x ⬝ succ y = (x ⬝ y) + x -/
def p_times_succ  : sentence L_peano := ∀' ∀' (&1 ×' succ &0 ≃ &1 ×' &0 +' &1)

@[reducible]def shallow_times_succ : Prop := ∀ x : ℕ, ∀ y : ℕ, x * (y + 1) = (x * y) + x

/- The induction schema instance at ψ is the following formula (up to the fixed ordering of variables given by the de Bruijn indexing):

letting k+1 be the number of free vars of ψ:

 (k ∀'s)[(ψ(...,0) ∧ ∀' (ψ → ψ(...,S(x)))) → ∀' ψ]
-/
def p_induction_schema {n : ℕ} (ψ : bounded_formula L_peano (n+1)) : sentence L_peano :=
bd_alls n (ψ[zero/0] ⊓ ∀' (ψ ⟹ (ψ ↑' 1 # 1)[succ &0/0]) ⟹ ∀' ψ)

@[reducible]def shallow_induction_schema : Π P : set ℕ, Prop := λ P, (P(0) ∧ ∀ x, P x → P (nat.succ x)) → ∀ x, P x

/- The theory of Peano arithmetic -/
def PA : Theory L_peano :=
{p_zero_not_succ, p_succ_inj, p_zero_is_identity, p_succ_plus, p_zero_of_times_zero, p_times_succ} ∪  ⋃ (n : ℕ), (λ(ψ : bounded_formula L_peano (n+1)), p_induction_schema ψ) '' set.univ

@[reducible]def shallow_PA : set Prop :=
{shallow_zero_not_succ, shallow_succ_inj, shallow_zero_is_identity, shallow_succ_plus, shallow_zero_of_times_zero, shallow_times_succ} ∪ (shallow_induction_schema '' (set.univ))

def is_even : bounded_formula L_peano 1 :=
∃' (&0 +' &0 ≃ &1)

def L_peano_structure_of_nat : Structure L_peano :=
begin
  refine ⟨ℕ, _, _⟩,
  {intros n F, induction F, exact λv, 0,
   {intro v, cases v, exact nat.succ v_x},
   {intro v, cases v, exact v_x + (v_xs.nth 0 $ by constructor)},
   {intro v, cases v, exact v_x * (v_xs.nth 0 $ by constructor)},},
  {intro v, intro R, cases R},
end

local notation `ℕ'` := L_peano_structure_of_nat

@[simp]lemma floris {L} {S : Structure L} : ↥S = S.carrier := by refl

example : ℕ' ⊨ p_zero_not_succ := begin
change ∀ x : ℕ', 0 = nat.succ x → false, intros x h, cases h end

@[simp]lemma zero_is_zero : @realize_bounded_term L_peano ℕ' 0 [] 0 zero [] = nat.zero := by refl
@[simp]lemma one_is_one : @realize_bounded_term L_peano ℕ' 0 [] 0 one [] = (nat.succ nat.zero)  := by refl

instance has_zero_sort_L_peano_structure_of_nat : has_zero ℕ' := ⟨nat.zero⟩

instance has_zero_L_peano_structure_of_nat : has_zero L_peano_structure_of_nat := ⟨nat.zero⟩

@[simp]lemma formal_nat_realize_term {n} : realize_closed_term ℕ' (formal_nat n) = n :=
  by {induction n, refl, tidy}

@[simp] lemma succ_realize_term {n} : realize_closed_term ℕ' (succ $ formal_nat n) = nat.succ n :=
begin
  dsimp[realize_closed_term, realize_bounded_term, succ, bounded_term_of_function],
  induction n, tidy
end

@[simp]lemma formal_nat_realize_formula {ψ : bounded_formula L_peano 1} (n) : realize_bounded_formula ([(n : ℕ')]) ψ [] ↔ ℕ' ⊨ ψ[(formal_nat n)/0] :=
begin
  induction n, all_goals{dsimp[formal_nat], simp[realize_subst_formula0]},
  have := @formal_nat_realize_term 0, unfold formal_nat at this, rw[this]
end

@[simp]lemma nat_bd_all {ψ : bounded_formula L_peano 1} : ℕ' ⊨ ∀'ψ ↔ ∀(n : ℕ'), ℕ' ⊨ ψ[(formal_nat n)/0] :=
begin
  refine ⟨by {intros H n, induction n, all_goals{dsimp[formal_nat], rw[realize_subst_formula0], tidy}}, _⟩,
  intros H n, have := H n, induction n, all_goals{simp only [formal_nat_realize_formula], exact this}
end

lemma shallow_induction (P : set nat) : (P(0) ∧ ∀ x, P x → P (nat.succ x)) → ∀ x, P x :=
  λ h, nat.rec h.1 h.2

section notation_test
-- #reduce (ℕ')[(@zero 0) /// [] ]


-- #reduce (L_peano_structure_of_nat)[(p_zero_not_succ)]

-- #reduce (L_peano_structure_of_nat)[(&0 ≃ zero : bounded_formula L_peano 1) ;; ([(1 : ℕ)] : dvector (ℕ') 1)] 

-- #reduce (&0 : bounded_term L_peano 1)[zero // 0] -- elaborator fails, don't know why
-- need to fix subst_bounded_term notation, something's not type-checking

end notation_test

-- @[simp]lemma subst0_subst0 {L} {n} {f : bounded_formula L (n+1)} {s₁} {s₂} : (f ↑' 1 # 1)[s₁ /0][s₂ /0] = f[s₁[s₂ /0] /0] := sorry -- this probably isn't true with careful lifting

-- @[simp]lemma subst_succ_is_apply {n} {k} : (succ &0)[formal_nat n /0] = @formal_nat k (nat.succ n) :=
-- begin
--   induction n, refl, symmetry, dsimp[formal_nat] at *, rw[<-n_ih],
--   unfold succ bounded_term_of_function formal_nat, tidy, induction n_n, tidy
-- end

-- @[simp]lemma subst_term'_cancel {n} {k} : Π ψ : bounded_formula L_peano (k + 1), (ψ ↑' 1 # 1)[succ &0 /0][formal_nat n /0] = ψ[formal_nat (nat.succ n) /0] := by simp
  
-- begin

--   -- intros n ψ, unfold subst0_bounded_formula, tidy, -- simp[lift_subst_formula_cancel ψ.fst 0],
--   -- sorry -- looks like here we need a lemma that generalizes lift_subst_formula_cancel to substitutions of terms, or something
-- end

---- oops, i think this is already somewhere in fol.lean
-- /-- Canonical extension of a dvector to a valuation --/
-- def val_of_dvector {α : Type*} [has_zero α] {n} (xs : dvector α n): ℕ' → α :=
-- begin
--   intro k,
--   by_cases nat.lt k n, 
--     exact xs.nth k h,
--     exact 0
-- end

/-- Given a term t with ≤ n free variables, the realization of t only depends on the nth initial segment of the realizing dvector v.  --/
-- lemma realize_closed_term_realize_irrel {L} {S : Structure L} {n n' : nat} {h : n' ≤ n} {t : bounded_term L n'} {v : dvector S n} : realize_bounded_term (dvector.trunc h v) t [] = realize_bounded_term v (t.cast h) [] :=
-- begin
--   revert t, apply bounded_term.rec, {intro k, induction k, induction v, have : n' = 0, by {apply nat.eq_zero_of_le_zero, exact h}, subst this, {tidy}, sorry},
--   tidy, sorry
-- end

-- lemma realize_closed_term_realizer_irrel {L} {S : Structure L} {n} {n'} {h : n' ≤ n} {t : bounded_term L n'} {v : dvector S n} : realize_bounded_term (@dvector.trunc n' n h xs) (t.cast (by simp)) [] = realize_bounded_term [] t [] :=
-- begin
--   induction n,
--      {cases v, revert t, },

--      {sorry},
-- end

-- lemma realize_bounded_formula_subst0_gen {L} {S : Structure L} {n l} (f : bounded_preformula L (n+1) l) {v : dvector S n} {xs : dvector S l} (t : bounded_term L n) : realize_bounded_formula v (f[(t.cast (by refl)) /0]) xs ↔ realize_bounded_formula ((realize_bounded_term v t [])::v) f xs :=
-- begin
--  sorry
-- end

-- realization of a substitution of a bounded_term (n' + 1) at n in a bounded_formula (n'' + 1), where n + n' = n'', is the same as realization (insert S[t])
-- lemma asjh {L} {S : Structure L} {n n' n''} {h : n + (n') + 1 = n'' + 1} {t : bounded_term L (n')} {f : bounded_formula L (n''+1)} {v : dvector S (n + n' + 1)} :
--   @realize_bounded_formula L S n 0 v (@subst_bounded_formula L n (n' + 1) (n'' + 1) 0 f t (by assumption) = @realize_bounded_formula L S (n+1) 0 (dvector.insert (realize_bounded_term begin end t)) sorry) sorry := sorry



/- ℕ' satisfies PA induction schema -/
theorem PA_standard_model_induction {index : nat} {ψ : bounded_formula L_peano (index + 1)} : ℕ' ⊨ bd_alls index (ψ[zero /0] ⊓ ∀'(ψ ⟹ (ψ ↑' 1 # 1)[succ &0 /0]) ⟹ ∀' ψ) :=
begin
  rw[realize_sentence_bd_alls], intro xs,
  simp,
  intros H_zero H_ih, apply nat.rec,
    {apply (realize_bounded_formula_subst0 ψ zero).mp, apply H_zero},
    {intros n H, apply (@realize_bounded_formula_subst0' _ _ _ ψ xs (succ &0) n).mp,
     exact H_ih n H}
end

def true_arithmetic := Th ℕ'

lemma true_arithmetic_extends_PA : PA ⊆ true_arithmetic :=
begin
  intros f hf, cases hf with not_induct induct,
  swap,
  {rcases induct with ⟨induction_schemas, ⟨⟨index, h_eq⟩, ih_right⟩⟩,
  rw [←h_eq] at ih_right, simp[set.range, set.image] at ih_right,
  rcases ih_right with ⟨ψ, h_ψ⟩, subst h_ψ, apply PA_standard_model_induction},
  {repeat{cases not_induct}, tidy, contradiction}
end

lemma shallow_standard_model : ∀ ψ ∈ shallow_PA, ψ :=
begin
  intros x H, cases H,
    {repeat{cases H}, tidy, contradiction},
    {simp[shallow_induction_schema] at H, rcases H with ⟨y, Hy⟩, subst Hy, exact nat.rec}
end

def PA_standard_model : Model PA := ⟨ℕ', true_arithmetic_extends_PA⟩

end PA
end peano

