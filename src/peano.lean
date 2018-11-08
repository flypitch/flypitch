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

--sanity check

-- #reduce quantifier_count_preformula 0 p_times_succ.fst

-- #reduce quantifier_count_preformula 0 p_zero_of_times_zero.fst  -- ok

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


def term_below_coe {L : Language} : ∀ {l}, Π n m : ℕ, (n ≤ m) → Π t :(preterm L l), (term_below n t) → (term_below m t)
  | _ n m _ &k _       := b_var' k begin dedup, cases _x_1, fapply lt_of_lt_of_le, exact n, repeat{assumption}  end
  | _ n m _ (func f) _                := term_below.b_func f
  | l n m _ (app t1 t2) _  :=  b_app' t1 t2 
                               begin
                               fapply term_below_coe, exact n, assumption, cases _x, assumption
                               end

                               begin
                               fapply term_below_coe, exact n, assumption, cases _x, assumption
                               end

def formula_below_coe {L : Language} : ∀ {l}, Π n m : ℕ, (n ≤ m) → Π f : preformula L l, formula_below n f → formula_below m f
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



/- both b_subst and b_subst2 are consequences of formula_below_subst in fol.lean -/
def b_subst {L : Language} {n : ℕ} {f : formula L} (hf : formula_below (n+1) f) {t : term L} (ht : term_below 0 t) : formula_below n (f[t //0]) :=
begin
have P := @formula_below_subst L 0 n 0 f begin simp, exact hf end t,
have t' : term_below n t,
  fapply term_below_coe,
  exact 0,
  exact n.zero_le,
  exact ht,
have Q := P t',
simp at Q, assumption
end

def b_subst2 {L : Language} {n : ℕ} {f : formula L} (hf : formula_below n f) {t : term L} (ht : term_below n t) : formula_below n (f[t //0]) :=
begin
have P := @formula_below_subst L 0 n 0 f begin simp, fapply formula_below_coe, exact n, simpa end t,
have P' := P ht, simp at P', assumption
end


/- END LEMMAS -/

/- The language of PA -/
inductive L_peano_funct : ℕ → Type -- thanks Floris!
| zero : L_peano_funct 0
| succ : L_peano_funct 1
| plus : L_peano_funct 2
| mult : L_peano_funct 2

--notation t ` ↑' `:90 n ` # `:90 m:90 := _root_.fol.lift_term_at t n m -- input ↑ with \u or \upa

def L_peano : Language := 
begin
split,
intro arityf,
exact L_peano_funct arityf,
exact λ n, empty
end

@[reducible] lemma peano_eq_mp_h {k : ℕ} : L_peano_funct k = L_peano.functions k := by refl

def L_peano_zero : L_peano.functions 0 := begin
fapply eq.mp, exact L_peano_funct 0, swap,
 exact L_peano_funct.zero, exact peano_eq_mp_h
end

def L_peano_succ : L_peano.functions 1 :=  begin
fapply eq.mp, exact L_peano_funct 1, swap,
 exact L_peano_funct.succ, exact peano_eq_mp_h
end

def L_peano_plus : L_peano.functions 2 :=  begin
fapply eq.mp, exact L_peano_funct 2, swap,
 exact L_peano_funct.plus, exact peano_eq_mp_h
end

def L_peano_mult : L_peano.functions 2 :=  begin
fapply eq.mp, exact L_peano_funct 2, swap,
 exact L_peano_funct.mult, exact peano_eq_mp_h
end


local infix  ` +' `:100 := bounded_term_of_function L_peano_plus

local infix ` ×' `:150 := bounded_term_of_function L_peano_mult

local notation `succ`:160 := bounded_term_of_function L_peano_succ

def zero {n} : bounded_term n := bd_const L_peano_zero

def one {n} : bounded_term n := succ zero

-- #check (fol.preterm.func L_peano_funct.zero) +' (fol.preterm.func begin fapply eq.mp, exact L_peano_funct 0, swap, exact L_peano_funct.zero, exact peano_eq_mp_h end)

/- for all x, zero not equal to succ x -/
def p_zero_not_succ : sentence L_peano :=
∀'(zero ≃ succ( &0) ⟹ ⊥)

def test1 := p_zero_not_succ.fst


def p_succ_inj : sentence L_peano := ∀' ∀'(succ &1 ≃ succ &0 ⟹ &1 ≃ &0)

def p_zero_is_identity : sentence L_peano := ∀'(&0 +' zero ≃ &0)

/- ∀ x ∀ y,  x + succ y = succ( x + y) -/
def p_succ_plus : sentence L_peano := ∀' ∀'(&1 +' (succ &0) ≃ succ (&1 +' &0))

/- ∀ x, x ⬝ 0 = 0 -/
def p_zero_of_times_zero : sentence L_peano := ∀'(&0 ×' zero ≃ zero)

/- ∀ x y, (x ⬝ succ y = (x ⬝ y) + x -/
/- ∀'∀'(app (app (func L_peano_funct.mult) &1) (app (func L_peano_funct.succ) &0) ≃
       app (app (func L_peano_funct.plus) (app (app (func L_peano_funct.mult) &1) &0)) &1)
-/
def p_times_succ  : sentence L_peano := ∀' ∀' (&1 ×' (succ &0) ≃ (&1 ×' &0) +' &1)

/- The induction schema instance at ψ is the following formula (up to the fixed ordering of variables given by the de Bruijn indexing):

 - let k be the number of free vars of k,

return (k - 1 ∀∀s)[(ψ(...,0) ∧ ∀' (ψ → ψ(...,S(x)))) → ∀' ψ]
-/
--ψ[succ(&0)/0]
def p_induction_schema {n : ℕ} (ψ : bounded_formula L_peano (n+1)) : sentence L_peano := -- add a hypothesis that ψ is in formula_below k and then do k_foralls
bd_alls n (ψ[zero/0] ⊓ (∀' (ψ ⟹ (ψ ↑' 1 # 1)[succ &0/0])) ⟹ ∀' ψ)
#print ⋃ 
#print set.Union
/- The theory of Peano arithmetic -/
def PA : Theory L_peano :=
{p_zero_not_succ, p_succ_inj, p_zero_is_identity, p_succ_plus, p_zero_of_times_zero, p_times_succ} ∪  ⋃ (n : ℕ), (λ(ψ : bounded_formula L_peano (n+1)), p_induction_schema ψ) '' set.univ


def is_even : bounded_formula L_peano 1 :=
∃' (&0 +' &0 ≃ &1)

def hewwo := (p_induction_schema is_even).fst

end
end peano

