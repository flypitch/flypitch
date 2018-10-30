import .fol tactic.tidy

open fol

local attribute [instance, priority 0] classical.prop_decidable

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

--sanity check

-- #reduce quantifier_count_preformula 0 p_times_succ.fst

-- #reduce quantifier_count_preformula 0 p_zero_of_times_zero.fst  -- ok

/-- Given a nat k and a 0-formula ψ, return ψ with ∀' applied k times to it --/ 
@[simp]def alls {L : Language}  :  Π n : ℕ, formula L → formula L
--:= nat.iterate all n
| 0 f := f
| (n+1) f := ∀' alls n f

@[simp] lemma alls_0 {L : Language} (ψ : formula L) : alls 0 ψ = ψ := by refl

@[simp] def b_alls_1 {L : Language} {n : ℕ} {f : formula L} (hf :  formula_below (n+1) f)  : formula_below n $ alls 1 f := begin
constructor, assumption
end

@[simp] lemma alls_all_commute {L : Language} (f : formula L) {k : ℕ} : (alls k ∀' f) = (∀' alls k f) :=
begin
induction k with k ih,
simp*,
simp* -- is this idiomatic?
end

@[simp] lemma alls_succ_k {L : Language} (f : formula L) {k : ℕ} : alls (k + 1) f = ∀' alls k f := by constructor

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


lemma term_below_coe {L : Language} : ∀ {l}, Π n m : ℕ, (n ≤ m) → Π t :(preterm L l), (term_below n t) → (term_below m t)
  | _ n m _ &k _       := b_var' k begin dedup, cases _x_1, fapply lt_of_lt_of_le, exact n, repeat{assumption}  end
  | _ n m _ (func f) _                := term_below.b_func f
  | l n m _ (app t1 t2) _  :=  b_app' t1 t2 
                               begin
                               fapply term_below_coe, exact n, assumption, cases _x, assumption
                               end

                               begin
                               fapply term_below_coe, exact n, assumption, cases _x, assumption
                               end

lemma formula_below_coe {L : Language} : ∀ {l}, Π n m : ℕ, (n ≤ m) → Π f : preformula L l, formula_below n f → formula_below m f
| _ n m _ falsum h := b_falsum
| _ n m _ (t1 ≃ t2) h := b_equal' t1 t2
                                  begin 
                                  cases h, fapply term_below_coe, exact n,
                                  repeat{assumption},
                                  end

                                  begin 
                                  cases h, fapply term_below_coe, exact n,
                                  repeat{assumption},
                                  end

| _ n m _ (rel R) h := b_rel R
| l n m _ (apprel f1 f2) h := b_apprel' f1 f2 
                                  begin 
                                  cases h, fapply formula_below_coe, exact n,
                                  swap, repeat{assumption}
                                  end

                                  begin 
                                  cases h, fapply term_below_coe, exact n,
                                  swap, repeat{assumption}
                                  end

| _ n m _ (f1 ⟹ f2) h := b_imp' f1 f2
                                  begin 
                                  cases h, fapply formula_below_coe, exact n,
                                  swap, repeat{assumption}
                                  end

                                  begin 
                                  cases h, fapply formula_below_coe, exact n,
                                  swap, repeat{assumption}
                                  end

| _ n m _ (∀' f) h := b_all' f
                                  begin 
                                  cases h, fapply formula_below_coe, exact n+1,
                                  swap, repeat{assumption}, simp*
                                  end



/- both b_subst and b_subst2 are defined, but i will refactor later -/
def b_subst {L : Language} {n : ℕ} {f : formula L} (hf : formula_below (n+1) f) {t : term L} (ht : term_below 0 t) : formula_below n (f[t //0]) :=
begin
cases hf,
constructor,
constructor,
cases hf_t₁,
simp[subst_term],
simp[subst_realize],
by_cases hf_t₁_1 < 0,
exfalso, fapply nat.not_lt_zero, exact hf_t₁_1, assumption,
simp*, cases hf_t₁_1, simp*, refine term_below_coe 0 n (nat.zero_le n) t ht, have hzerolt : 0 < nat.succ hf_t₁_1, by apply nat.zero_lt_succ, simp*, simp* at hf_ht₁, cases hf_ht₁,
have : hf_t₁_1 < n, sorry, -- yuck, need to reorganize
repeat {sorry}
end

def b_subst2 {L : Language} {n : ℕ} {f : formula L} (hf : formula_below n f) {t : term L} (ht : term_below n t) : formula_below n (f[t //0]) := sorry


/- The induction schema instance at ψ is the following formula (up to the fixed ordering of variables given by the de Bruijn indexing):

 - let k be the number of free vars of k,

return (k - 1 ∀∀s)[(ψ(...,0) ∧ (k ∀∀s) (ψ → ψ(...,S(x)))) → (k ∀∀s) ψ]
-/

/- END LEMMAS -/

/- The language of PA -/
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

@[reducible] lemma duh : peano_f1 = L_peano.functions 1 := by refl

#reduce (all (&0 ≃ &1))[begin apply app, apply func, exact eq.mp duh peano_f1.succ, exact &0 end // 0]


def p_zero_not_succ : @sentence L_peano :=
begin
split, swap,
  begin
  apply all, apply fol.not, apply equal, apply func, exact peano_f0.zero,
  apply app, apply func, exact peano_f1.succ, exact &0
  end,
repeat{constructor}
end

def test1 := p_zero_not_succ.fst

#reduce test1


def p_succ_inj : @sentence L_peano :=
begin
split,swap,
  begin
  apply all, apply all, apply imp, apply equal, apply app, apply func, exact peano_f1.succ, exact &1, apply app, apply func, exact peano_f1.succ, exact &0, apply equal, exact &1, exact &0
  end,
repeat{constructor}
end

def hewwo := p_succ_inj.fst

#reduce hewwo

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

def p_induction_schema (n : ℕ) (ψ : formula L_peano) (hψ : formula_below n ψ)  : @sentence L_peano := -- add a hypothesis that ψ is in formula_below k and then do k_foralls
begin
--  let k := free_var_count 0 ψ,
split,swap,

  begin
  apply alls (n-1), apply imp, apply fol.and, refine ψ[_//0], apply func, exact peano_f0.zero, apply all, apply imp, exact ψ, refine ψ[_ //0], apply app, apply func, exact peano_f1.succ, exact &0, apply alls (n), exact ψ
  end,
  
  apply b_alls_k,
  repeat{constructor},
  
  begin
  simp, apply b_subst, by_cases n = 0, simp*,
  rw[h] at hψ, fapply formula_below_coe, exact 0, apply nat.zero_le, assumption,
  simp*, have : (1 + (n - 1)) = n,
  cases n, exfalso, finish, simp*, rw[this], assumption,
  constructor
  end,

  begin 
  by_cases n = 0, simp*,
  rw[h] at hψ, fapply formula_below_coe, exact 0, apply nat.zero_le, assumption, simp*, have : (1 + (n - 1)) = n,
  cases n, exfalso, finish, simp*, rw[this], assumption,
  end,

  begin
  simp, apply b_subst2, by_cases n = 0, simp*,
  rw[h] at hψ, fapply formula_below_coe, exact 1, simp,
  fapply formula_below_coe, exact 0, apply nat.zero_le, assumption, have : (1 + (n - 1)) = n,
  cases n, exfalso, finish, simp*, rw[this], assumption,
  constructor, constructor, constructor,
  cases n, tidy
  end,

  begin
  apply b_alls_k, by_cases n = 0, rw[h], rw[h] at hψ, assumption,
  fapply formula_below_coe, exact n, simp, apply nat.zero_le, assumption
  end
end

--   apply b_alls_k,
--   apply b_imp, apply b_and, swap, apply b_all, apply b_imp, swap,
  
--   begin
--   simp, apply b_apply_at_variable,/-b_subst2-/
--   by_cases n = 0,
--   rw[h] at hψ, fapply formula_below_coe, exact 0, simpa,
--   have : (1 + (n - 1)) = n,
--     by
--       begin
-- --      simp,
--       cases n,
--       finish,
--       tidy
--       end,
--   rw[this],
--   fapply formula_below_coe, exact n, simpa,

--   -- apply term_below.b_app, apply term_below.b_func,
--   -- apply term_below.b_var, cases n,
--   -- simp*,
--   end,

--   begin
--   by_cases n = 0,
--   rw[h], rw[h] at hψ,
--   simp*, fapply formula_below_coe, exact 0, simpa,

--   simp*, assumption
--   end,

--   begin
--   by_cases n = 0,
--   apply b_subst,
--   simp*, rw[h] at hψ,
--   fapply formula_below_coe, exact 0, simpa,
  
--   constructor,
--   apply b_subst,
--   simp*, assumption,

--   constructor
--   end,

--   begin
--   apply b_alls_k, simp*, fapply formula_below_coe, exact n, simp*, assumption
--   end
-- end




end
end peano

