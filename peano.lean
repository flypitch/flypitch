import .language_term_n2 tactic.tidy

open fol


namespace peano
section

inductive peano_f0
| zero
| one

inductive peano_f1
| succ

inductive peano_f2
| plus
| mult


def L_peano : Language := 
begin
split,
intro arityf,
exact if arityf = 0 then peano_f0
                else if arityf = 1 then peano_f1
                else if arityf = 2 then peano_f2
                else empty,
exact λ n, empty
end

/- Axioms of Peano Arithmetic -/

def p_zero_not_succ : @sentence L_peano :=
begin
split, swap,
  begin
  apply all, apply fol.not, apply equal, apply func, exact peano_f0.zero,
  apply app, apply func, exact peano_f1.succ, exact &0
  end,
repeat{constructor}
end

def p_succ_inj : @sentence L_peano :=
begin
split,swap,
  begin
  apply all, apply all, apply imp, apply equal, apply app, apply func, exact peano_f1.succ, exact &1, apply app, apply func, exact peano_f1.succ, exact &0, apply equal, exact &1, exact &0
  end,
repeat{constructor}
end

def p_zero_is_identity : @sentence L_peano :=
begin
split, swap,
  begin
  apply all, apply equal, apply app, apply app, apply func, exact peano_f2.plus, exact &0, apply func, exact peano_f0.zero, exact &0
  end,
repeat{constructor}
end

/- ∀ x ∀ y,  x + succ y = succ( x + y) -/
def p_succ_plus : @sentence L_peano :=
begin
split, swap,
  begin
  apply all, apply all, apply equal, apply app, apply app, apply func, exact peano_f2.plus, exact &1, apply app, apply func, exact peano_f1.succ, exact &0, apply app, apply func, exact peano_f1.succ, apply app, apply app, apply func, exact peano_f2.plus, exact &1, exact &0
  end,
repeat{constructor}
end

/- ∀ x, x ⬝ 0 = 0 -/
def p_zero_of_times_zero : @sentence L_peano :=
begin
split, swap,
  begin
  apply all, apply equal, apply app, apply app, apply func, exact peano_f2.mult, exact &0, apply func, exact peano_f0.zero, apply func, exact peano_f0.zero
  end,
repeat{constructor}
end

/- ∀ x y, (x ⬝ succ y = (x ⬝ y) + x -/
def p_times_succ  : @sentence L_peano :=
begin
split, swap,
  begin
  apply all, apply all, apply equal, apply app, apply app, apply func, exact peano_f2.mult, exact &1, apply app, apply func, exact peano_f1.succ, exact &1, apply app, apply app, apply func, exact peano_f2.plus, apply app, apply app, apply func, exact peano_f2.mult, exact &1, exact &0, exact &1
  end,
repeat{constructor}
end

/- Induction schema -/

--TODO: finish this

def var_list_preterm {L : Language} : Π n : ℕ, preterm L n → list ℕ
| 0 (var k) := [k]
| n (func f) := list.nil
| n (app t1 t2) := var_list_preterm _ t1 ∪ var_list_preterm _ t2

def var_list_preformula {L : Language} : Π n : ℕ, preformula L n → list ℕ
| 0 falsum := list.nil
| 0 (equal t1 t2) := var_list_preterm _ t1 ∪ var_list_preterm _ t2
| n (rel R) := list.nil
| n (apprel t1 t2) := var_list_preformula _ t1 ∪ var_list_preterm _ t2
| 0 (f1 ⟹ f2) := var_list_preformula _ f1 ∪ var_list_preformula _ f2
| 0 (∀' f) := var_list_preformula _ f
 
def quantifier_count_preterm {L : Language} : Π n, preterm L n → ℕ := λ n, λ t, 0


def quantifier_count_preformula {L : Language} : Π n, preformula L n → ℕ
| 0 falsum := 0
| 0 (equal t1 t2) := quantifier_count_preterm _ t1 + quantifier_count_preterm _ t2
| n (rel R) := 0
| n (apprel t1 t2) := quantifier_count_preformula _ t1 + quantifier_count_preterm _ t2
| 0 (f1 ⟹ f2) := quantifier_count_preformula _ f1 + quantifier_count_preformula _ f2
| 0 (∀' f) := quantifier_count_preformula _ f + 1


def free_var_count {L : Language} (n : ℕ) : preformula L n → ℕ :=
λ ψ, max 0 $ (var_list_preformula n ψ).length - quantifier_count_preformula n ψ

--sanity check

#reduce quantifier_count_preformula 0 p_times_succ.fst

#reduce quantifier_count_preformula 0 p_zero_of_times_zero.fst  -- awesome

#reduce var_list_preformula 0 p_times_succ.fst

#reduce var_list_preformula 0 p_zero_of_times_zero.fst  -- awesome

#reduce free_var_count 0 p_times_succ.fst -- yes!!

/-- Given a nat k and a 0-formula ψ, return ψ with ∀' applied k times to it --/
@[simp]def alls {L : Language} : Π n : ℕ, formula L → formula L
| 0 ψ := ψ
| (n+1) ψ := ∀' (alls n ψ)

/-- Return the highest variable in ψ --/
def highest_variable {L : Language} : Π n, preformula L n → ℕ :=
begin
intros n ψ,
exact list.foldr max 0 (var_list_preformula n ψ)
end

@[simp] lemma alls_0 {L : Language} (ψ : formula L) : alls 0 ψ = ψ := by refl

@[simp] def b_alls_1 {L : Language} {n : ℕ} {f : formula L} (hf :  formula_below (n+1) f)  : formula_below n $ alls 1 f := begin
constructor, simp*, assumption
end

@[simp] lemma alls_succ_k {L : Language} (f : formula L) {k : ℕ} : alls (k + 1) f = ∀' alls k f := by constructor

@[simp] lemma alls_all_commute {L : Language} (f : formula L) {k : ℕ} : (alls k ∀' f) = (∀' alls k f) :=
begin
induction k with k ih,
simp*,
simp* -- is this idiomatic?
end

@[simp] def b_alls_k {L : Language} {n : ℕ} {k: ℕ} :  ∀ f : formula L, formula_below (n + k) f → formula_below n (alls k f) :=
begin
-- induction n with n ih, induction k with k ih,
induction k with k ih,
intros f hf, exact hf,
intros f hf, 
have H := alls_succ_k,

have hf_rw : formula_below (n + nat.succ k) f → formula_below (n+k) ∀'f, by {apply b_alls_1},
let hf2 := hf_rw hf,

have hooray := ih (∀'f) hf2,
rw[alls_all_commute, <-H] at hooray, exact hooray --hooray!!
end

/- The induction schema instance at ψ is the following formula (up to the fixed ordering of variables given by the de Bruijn indexing):

 - let k be the number of free vars of k,

return (k - 1 ∀∀s)[(ψ(...,0) ∧ (k ∀∀s) (ψ → ψ(...,S(x)))) → (k ∀∀s) ψ]
-/

set_option trace.app_builder true

def p_induction_schema (ψ : formula L_peano) : @sentence L_peano :=
begin
  let k := free_var_count 0 ψ,
split,swap,
  begin
  apply alls (k-1), apply imp, apply fol.and, refine ψ[_//0], apply func, exact peano_f0.zero, apply all, apply imp, exact ψ, refine ψ[_//0], apply app, apply func, exact peano_f1.succ, exact &(highest_variable 0 ψ), apply alls (k), exact ψ
  end,
dsimp[k],
simp[free_var_count],
apply b_alls_k,
simp*,
repeat{constructor},
{sorry},
{sorry},
{sorry},
{sorry}
end

end
end peano
