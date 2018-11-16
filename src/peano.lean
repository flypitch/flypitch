import .fol tactic.tidy

open fol

local attribute [instance, priority 0] classical.prop_decidable
--local attribute [instance] classical.prop_decidable

namespace peano
section
 
def quantifier_count_preterm {L : Language} : Π n, preterm L n → ℕ := λ n, λ t, 0

def quantifier_count_preformula {L : Language} : Π n, preformula L n → ℕ
| 0 falsum := 0
| 0 (equal t1 t2) := quantifier_count_preterm _ t1 + quantifier_count_preterm _ t2
| n (rel R) := 0
| n (apprel t1 t2) := quantifier_count_preformula _ t1 + quantifier_count_preterm _ t2
| 0 (f1 ⟹ f2) := quantifier_count_preformula _ f1 + quantifier_count_preformula _ f2
| 0 (∀' f) := quantifier_count_preformula _ f + 1

/-- Given a nat k and a 0-formula ψ, return ψ with ∀' applied k times to it --/ 
@[simp] def alls {L : Language}  :  Π n : ℕ, formula L → formula L
--:= nat.iterate all n
| 0 f := f
| (n+1) f := ∀' alls n f

@[simp] def bd_alls {L : Language}  : Π n : ℕ, bounded_formula L n → bounded_formula L 0
| 0     f := f
| (n+1) f := bd_alls n (∀' f)

@[simp] lemma alls_0 {L : Language} (ψ : formula L) : alls 0 ψ = ψ := by refl

@[simp] def b_alls_1 {L : Language} {n : ℕ} {f : formula L} (hf :  formula_below (n+1) f)  : formula_below n $ alls 1 f := begin
constructor, assumption
end

@[simp] lemma alls_all_commute {L : Language} (f : formula L) {k : ℕ} : (alls k ∀' f) = (∀' alls k f) :=
begin
induction k with k ih,
simp only [peano.alls, nat.nat_zero_eq_zero, peano.alls_0, eq_self_iff_true],
simpa only [peano.alls, eq_self_iff_true] -- is this idiomatic?
end

@[simp] lemma alls_succ_k {L : Language} (f : formula L) {k : ℕ} : alls (k + 1) f = ∀' alls k f := by constructor

@[simp] def b_alls_k {L : Language} {n : ℕ} {k: ℕ} :  ∀ f : formula L, formula_below (n + k) f → formula_below n (alls k f) :=
begin
  induction k with k ih,
  intros f hf, exact hf,
  intros f hf, 
  have H := alls_succ_k,

  have hf_rw : formula_below (n + nat.succ k) f → formula_below (n+k) ∀'f, by {apply b_alls_1},
  let hf2 := hf_rw hf,

  have hooray := ih (∀'f) hf2,
  rw[alls_all_commute, <-H] at hooray, exact hooray --hooray!!
end

/- both b_subst and b_subst2 are consequences of formula_below_subst in fol.lean -/
def b_subst {L : Language} {n : ℕ} {f : formula L} (hf : formula_below (n+1) f) {t : term L} (ht : term_below 0 t) : formula_below n (f[t //0]) :=
begin
have P := @formula_below_subst L 0 n 0 f begin rw[zero_add], exact hf end t,
have t' : term_below n t,
  fapply term_below_of_le,
  exact 0,
  exact n.zero_le,
  exact ht,
have Q := P t',
simp only [fol.subst_formula, zero_add] at Q, assumption
end

def b_subst2 {L : Language} {n : ℕ} {f : formula L} (hf : formula_below n f) {t : term L} (ht : term_below n t) : formula_below n (f[t //0]) :=
begin
  have P := @formula_below_subst L 0 n 0 f begin rw[zero_add], fapply formula_below_of_le, exact n, simpa end t,
  have P' := P ht, simp only [fol.subst_formula, zero_add] at P', assumption
end


/- END LEMMAS -/

/- The language of PA -/
inductive L_peano_funct : ℕ → Type -- thanks Floris!
| zero : L_peano_funct 0
| succ : L_peano_funct 1
| plus : L_peano_funct 2
| mult : L_peano_funct 2

--notation t ` ↑' `:90 n ` # `:90 m:90 := _root_.fol.lift_term_at t n m -- input ↑ with \u or \upa

def L_peano : Language := ⟨L_peano_funct, λ n, empty⟩

def L_peano_zero : L_peano.functions 0 := L_peano_funct.zero
def L_peano_succ : L_peano.functions 1 := L_peano_funct.succ
def L_peano_plus : L_peano.functions 2 := L_peano_funct.plus
def L_peano_mult : L_peano.functions 2 := L_peano_funct.mult

local infix ` +' `:100 := bounded_term_of_function L_peano_plus
local infix ` ×' `:150 := bounded_term_of_function L_peano_mult

def succ {n} : bounded_term L_peano n → bounded_term L_peano  n := bounded_term_of_function L_peano_succ
def zero {n} : bounded_term L_peano n := bd_const L_peano_zero
def one {n} : bounded_term L_peano n := succ zero

/- for all x, zero not equal to succ x -/
def p_zero_not_succ : sentence L_peano :=
∀'(zero ≃ succ &0 ⟹ ⊥)

def p_succ_inj : sentence L_peano := ∀' ∀'(succ &1 ≃ succ &0 ⟹ &1 ≃ &0)

def p_zero_is_identity : sentence L_peano := ∀'(&0 +' zero ≃ &0)

/- ∀ x ∀ y,  x + succ y = succ( x + y) -/
def p_succ_plus : sentence L_peano := ∀' ∀'(&1 +' succ &0 ≃ succ (&1 +' &0))

/- ∀ x, x ⬝ 0 = 0 -/
def p_zero_of_times_zero : sentence L_peano := ∀'(&0 ×' zero ≃ zero)

/- ∀ x y, (x ⬝ succ y = (x ⬝ y) + x -/
def p_times_succ  : sentence L_peano := ∀' ∀' (&1 ×' succ &0 ≃ &1 ×' &0 +' &1)

/- The induction schema instance at ψ is the following formula (up to the fixed ordering of variables given by the de Bruijn indexing):

 - let k+1 be the number of free vars of ψ,

return (k ∀∀s)[(ψ(...,0) ∧ ∀' (ψ → ψ(...,S(x)))) → ∀' ψ]
-/
def p_induction_schema {n : ℕ} (ψ : bounded_formula L_peano (n+1)) : sentence L_peano :=
bd_alls n (ψ[zero/0] ⊓ ∀' (ψ ⟹ (ψ ↑' 1 # 1)[succ &0/0]) ⟹ ∀' ψ)

/- The theory of Peano arithmetic -/
def PA : Theory L_peano :=
{p_zero_not_succ, p_succ_inj, p_zero_is_identity, p_succ_plus, p_zero_of_times_zero, p_times_succ} ∪  ⋃ (n : ℕ), (λ(ψ : bounded_formula L_peano (n+1)), p_induction_schema ψ) '' set.univ

def is_even : bounded_formula L_peano 1 :=
∃' (&0 +' &0 ≃ &1)

def hewwo := (p_induction_schema is_even).fst

def L_peano_structure_of_nat : Structure L_peano :=
begin
  refine ⟨ℕ, _, _⟩,
  {intros n F, cases F with zero succ plus mult, exact λv, 0,
   {intro v, cases v, exact nat.succ v_x},
   {intro v, cases v, exact v_x + (v_xs.nth 0 $ by constructor)},
   {intro v, cases v, exact v_x * (v_xs.nth 0 $ by constructor)},
   },
  {intro v, intro R, cases R},
end

local notation ℕ := L_peano_structure_of_nat

@[simp]lemma floris {L} {S : Structure L} : ↥S = S.carrier := by refl

example : ℕ ⊨ p_zero_not_succ := begin
change ∀ x : ℕ, 0 = nat.succ x → false, intro x, intro h, cases h end

-- TODO, try proving the induction schema for a simple case.

def PA_standard_model : Model PA :=
begin
  refine ⟨ℕ, _⟩,
  unfold all_realize_sentence, intros f hf, cases hf with not_induct induct,
  repeat{cases not_induct},
  {tidy}, {tidy}, {tidy}, {tidy}, {tidy},
  {tidy, cases a},
  {cases induct with induction_schemas ih, simp[*, -ih] at ih, cases ih with ih_left ih_right,
    cases ih_left with index h_eq, rw[h_eq] at ih_right, unfold set.range at ih_right,
    cases ih_right with ψ h_ψ, rw[<-h_ψ], unfold p_induction_schema,
    -- phew, finally got the goal to be, literally show some instance of the induction schema
    induction index, simp*, intros H1 H2,
    {intro x, induction x, refine (realize_subst_formula0 _ _ zero).mp _, exact H1, -- have := H2 x, simp[realize_bounded_formula, realize_formula_below] at *, 
    },
    {sorry},
  }
end

local notation ℕ := PA_standard_model

end
end peano
