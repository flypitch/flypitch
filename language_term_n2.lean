namespace tactic
namespace interactive
meta def congr1 : tactic unit := congr_core
end interactive
end tactic

namespace fol
structure Language := 
(relations : ℕ → Type) (functions : ℕ → Type) (equal : relations 2) (false : relations 0)
section
parameter {L : Language}

/- preterm n is a partially applied term. if applied to n terms, it becomes a term -/
inductive preterm : ℕ → Type 
| var : ℕ → preterm 0
| func : ∀ {n : nat}, L.functions n → preterm n
| apply : ∀ {n : nat}, preterm (n + 1) → preterm 0 → preterm n
open preterm
@[reducible] def term := preterm 0

local prefix `&`:max := var

/- lift_term_at _ t n m raises variables in t which are at least m by n -/
@[simp] def lift_term_at : ∀ {l}, preterm l → ℕ → ℕ → preterm l
| _ (var k)       n m := if m ≤ k then var (k+n) else var k
| _ (func f)      n m := func f
| _ (apply t1 t2) n m := apply (lift_term_at t1 n m) (lift_term_at t2 n m)

local notation t ` ↑ `:55 n ` # `:55 m:55 := lift_term_at t n m

def lift_term (t : term) (n : ℕ) : term := t ↑ n # 0
def lift_term1 (t : term) : term := t ↑ 1 # 0

lemma lift_term_at_inj : ∀ {l} {t t' : preterm l} {n m : ℕ}, t ↑ n # m = t' ↑ n # m → t = t'
| _ (var k) (var k')          n m h := 
  by by_cases h₁ : m ≤ k; by_cases h₂ : m ≤ k'; simp [h₁, h₂] at h; congr; 
       [exact add_right_cancel h, skip, skip, assumption]; exfalso; 
       try {apply h₁}; try {apply h₂}; subst h; 
       apply le_trans (by assumption) (nat.le_add_right _ _)
| _ (var k) (func f')         n m h := by by_cases h' : m ≤ k; simp [h'] at h; contradiction
| _ (var k) (apply t1' t2')   n m h := by by_cases h' : m ≤ k; simp [h'] at h; contradiction
| _ (func f) (var k')         n m h := by by_cases h' : m ≤ k'; simp [h'] at h; contradiction
| _ (func f) (func f')        n m h := h
| _ (func f) (apply t1' t2')  n m h := by cases h
| _ (apply t1 t2) (var k')    n m h := by by_cases h' : m ≤ k'; simp [h'] at h; contradiction
| _ (apply t1 t2) (func f')   n m h := by cases h
| _ (apply t1 t2) (apply t1' t2') n m h := 
  begin injection h, congr; apply lift_term_at_inj; assumption end

@[simp] lemma lift_term_at_zero : ∀ {l} (t : preterm l) (m : ℕ), t ↑ 0 # m = t
| _ (var k)     m := by simp
| _ (func f)      m := by refl
| _ (apply t1 t2) m := by dsimp; congr; apply lift_term_at_zero

/- the following lemmas simplify iterated lifts, depending on the size of m' -/
lemma lift_term_at2_small : ∀ {l} (t : preterm l) (n n') {m m'}, m' ≤ m → 
  (t ↑ n # m) ↑ n' # m' = (t ↑ n' # m') ↑ n # (m + n')
| _ (var k)       n n' m m' H := 
  begin 
    by_cases h : m ≤ k,
    { have h₁ : m' ≤ k, from le_trans H h,
      have h₂ : m' ≤ k + n, from le_trans h₁ (k.le_add_right n),
      have h₃ : m + n' ≤ k + n', from add_le_add_right h _,
      simp [h, h₁, h₂, h₃, -add_assoc, -add_comm], simp },
    { have h₁ : ¬m + n' ≤ k + n', from λ h', h (le_of_add_le_add_right h'),
      have h₂ : ¬m + n' ≤ k, from λ h', h₁ (le_trans h' (k.le_add_right n')),
      by_cases h' : m' ≤ k; simp [h, h', h₁, h₂, -add_comm, -add_assoc], }
  end
| _ (func f)      n n' m m' H := by refl
| _ (apply t1 t2) n n' m m' H := 
  begin dsimp; congr1; apply lift_term_at2_small; assumption end

lemma lift_term_at2_medium : ∀ {l} (t : preterm l) (n n') {m m'}, m ≤ m' → m' ≤ m+n → 
  (t ↑ n # m) ↑ n' # m' = t ↑ (n+n') # m
| _ (var k)       n n' m m' H₁ H₂ := 
  begin 
    by_cases h : m ≤ k,
    { have h₁ : m' ≤ k + n, from le_trans H₂ (add_le_add_right h n),
      simp [h, h₁, -add_comm], },
    { simp[h, -add_assoc, -add_comm],
      have h₁ : ¬m' ≤ k, from λ h', h (le_trans H₁ h'),
      simp [h, h₁, -add_comm, -add_assoc] }
  end
| _ (func f)      n n' m m' H₁ H₂ := by refl
| _ (apply t1 t2) n n' m m' H₁ H₂ := 
  begin dsimp; congr1; apply lift_term_at2_medium; assumption end

lemma lift_term_at2_eq {l} (t : preterm l) (n n' m : ℕ) : 
  (t ↑ n # m) ↑ n' # (m+n) = t ↑ (n+n') # m :=
lift_term_at2_medium t n n' (m.le_add_right n) (le_refl _)

lemma lift_term_at2_large {l} (t : preterm l) (n n') {m m'} (H : m' ≥ m + n) : 
  (t ↑ n # m) ↑ n' # m' = (t ↑ n' # m'-n) ↑ n # m :=
have H₁ : n ≤ m', from le_trans (n.le_add_left m) H,
have H₂ : m ≤ m' - n, by rw [←nat.add_sub_cancel m n]; apply nat.sub_le_sub_right; exact H,
begin rw fol.lift_term_at2_small t n' n H₂, rw [nat.sub_add_cancel], exact H₁ end

/- substitute_term t s n substitutes s for (var n) and reduces the level of all variables above n by 1 -/
@[simp] def substitute_term : ∀ {l}, preterm l → term → ℕ → preterm l
| _ (var k)     s n := if k < n then var k else if n < k then var (k-1) else s
| _ (func f)      s n := func f
| _ (apply t1 t2) s n := apply (substitute_term t1 s n) (substitute_term t2 s n)

@[simp] def substitute_term_var_eq (t : term) (n : ℕ) : substitute_term &n t n = t :=
by simp [lt_irrefl]

lemma substitute_term_lift_term' : ∀{l} (t : preterm l) (s : term), 
  substitute_term (lift_term_at t 1 0) s 0 = t :=
sorry

@[simp] lemma substitute_term_lift_term (t s : term) : substitute_term (lift_term1 t) s 0 = t :=
substitute_term_lift_term' t s

/- preformula n is a partially applied formula. if applied to n terms, it becomes a formula -/
inductive preformula : ℕ → Type 
| rel : ∀ {n : nat}, L.relations n → preformula n
| apprel : ∀ {n : nat}, preformula (n + 1) → term → preformula n
| imp : preformula 0 → preformula 0 → preformula 0
| all : preformula 0 → preformula 0
open preformula
def formula := preformula 0

def equal (t₁ t₂ : term) : formula := apprel (apprel (rel L.equal) t₁) t₂
def false : formula := rel L.false
def not (f : formula) : formula := imp f false
def or (f₁ f₂ : formula) : formula := imp (not f₁) f₂
def and (f₁ f₂ : formula) : formula := not (imp f₁ (not f₂))
def iff (f₁ f₂ : formula) : formula := and (imp f₁ f₂) (imp f₂ f₁)
def ex (f : formula) : formula := not (all (not f))

local infix ` ⟾ `:70 := imp
local infix ` ⇔ `:75 := iff
local infix ` ≍ `:80 := equal

@[simp] def lift_formula_at : ∀ {l}, preformula l → ℕ → ℕ → preformula l
| _ (rel R)      n m := rel R
| _ (apprel f t) n m := apprel (lift_formula_at f n m) (lift_term_at t n m)
| _ (imp f1 f2)  n m := imp (lift_formula_at f1 n m) (lift_formula_at f2 n m)
| _ (all f)      n m := all (lift_formula_at f n (m+1))

local notation f ` ↑ `:55 n ` # `:55 m:55 := lift_formula_at f n m

def lift_formula (f : formula) (n : ℕ) : formula := f ↑ n # 0
def lift_formula1 (f : formula) : formula := f ↑ 1 # 0

lemma lift_formula_at_inj {l} {f f' : preformula l} {n m : ℕ} (H : f ↑ n # m = f' ↑ n # m) : f = f' :=
begin
  induction f generalizing m; cases f'; injection H,
  simp [f_ih h_1, fol.lift_term_at_inj h_2],
  simp [f_ih_a h_1, f_ih_a_1 h_2],
  simp [f_ih h_1]
end

@[simp] lemma lift_formula_at_zero : ∀ {l} (f : preformula l) (m : ℕ), f ↑ 0 # m = f
| _ (rel R)      m := by refl
| _ (apprel f t) m := by simp; apply lift_formula_at_zero
| _ (imp f1 f2)  m := by dsimp; congr1; apply lift_formula_at_zero
| _ (all f)      m := by simp; apply lift_formula_at_zero

/- the following lemmas simplify iterated lifts, depending on the size of m' -/
lemma lift_formula_at2_small : ∀ {l} (f : preformula l) (n n') {m m'}, m' ≤ m → 
  (f ↑ n # m) ↑ n' # m' = (f ↑ n' # m') ↑ n # (m + n')
| _ (rel R)      n n' m m' H := by refl
| _ (apprel f t) n n' m m' H := 
  by simp [lift_term_at2_small, H, -add_comm]; apply lift_formula_at2_small; assumption
| _ (imp f1 f2)  n n' m m' H := by dsimp; congr1; apply lift_formula_at2_small; assumption
| _ (all f)      n n' m m' H :=
  by simp [lift_term_at2_small, H, lift_formula_at2_small f n n' (add_le_add_right H 1)]

lemma lift_formula_at2_medium : ∀ {l} (f : preformula l) (n n') {m m'}, m ≤ m' → m' ≤ m+n → 
  (f ↑ n # m) ↑ n' # m' = f ↑ (n+n') # m
| _ (rel R)      n n' m m' H₁ H₂ := by refl
| _ (apprel f t) n n' m m' H₁ H₂ :=
  by simp [lift_term_at2_medium, H₁, H₂, -add_comm]; apply lift_formula_at2_medium; assumption
| _ (imp f1 f2)  n n' m m' H₁ H₂ := by dsimp; congr1; apply lift_formula_at2_medium; assumption
| _ (all f)      n n' m m' H₁ H₂ :=
  have m' + 1 ≤ (m + 1) + n, from le_trans (add_le_add_right H₂ 1) (by simp),
  by simp [lift_term_at2_medium, H₁, H₂, lift_formula_at2_medium f n n' (add_le_add_right H₁ 1) this]

lemma lift_formula_at2_eq {l} (f : preformula l) (n n' m : ℕ) : 
  (f ↑ n # m) ↑ n' # (m+n) = f ↑ (n+n') # m :=
lift_formula_at2_medium f n n' (m.le_add_right n) (le_refl _)

lemma lift_formula_at2_large {l} (f : preformula l) (n n') {m m'} (H : m' ≥ m + n) : 
  (f ↑ n # m) ↑ n' # m' = (f ↑ n' # m'-n) ↑ n # m :=
have H₁ : n ≤ m', from le_trans (n.le_add_left m) H,
have H₂ : m ≤ m' - n, by rw [←nat.add_sub_cancel m n]; apply nat.sub_le_sub_right; exact H,
begin rw fol.lift_formula_at2_small f n' n H₂, rw [nat.sub_add_cancel], exact H₁ end

@[simp] def substitute_formula : ∀ {l}, preformula l → term → ℕ → preformula l
| _ (rel R)      s n := rel R
| _ (apprel f t) s n := apprel (substitute_formula f s n) (substitute_term t s n)
| _ (imp f1 f2)  s n := imp (substitute_formula f1 s n) (substitute_formula f2 s n)
| _ (all f)      s n := all (substitute_formula f s (n+1))

@[simp] def substitute_formula0 (f : formula) (t : term) := substitute_formula f t 0

@[simp] def substitute_formula_equal (t₁ t₂ s : term) (n : ℕ) :
  substitute_formula (t₁ ≍ t₂) s n = substitute_term t₁ s n ≍ substitute_term t₂ s n :=
by refl

-- ⟾⇔≍

inductive prf : list formula → formula → Type
| axm    : ∀{Γ A}, A ∈ Γ → prf Γ A
| impI   : ∀{Γ A B}, prf (A::Γ) B → prf Γ (A ⟾ B)
| impE   : ∀{Γ A B}, prf Γ (A ⟾ B) → prf Γ A → prf Γ B
| falseE : ∀{Γ A}, prf (not A::Γ) false → prf Γ A
| allI   : ∀{Γ A}, prf (list.map lift_formula1 Γ) A → prf Γ (all A)
| allE   : ∀{Γ} A t, prf Γ (all A) → prf Γ (substitute_formula0 A t)
| refl   : ∀Γ t, prf Γ (t ≍ t)
| subst : ∀{Γ} s t f, prf Γ (s ≍ t) → prf Γ (substitute_formula f s 0) → 
  prf Γ (substitute_formula f t 0)
open prf
local infix ` ⊢ `:51 := prf

def symm {Γ s t} (H : Γ ⊢ s ≍ t) : Γ ⊢ t ≍ s :=
begin 
  have H₁ := subst s t (equal (var 0) (lift_term1 s)) H, -- why does notation not work here?
  rw [substitute_formula_equal, substitute_formula_equal, substitute_term_lift_term, substitute_term_lift_term, substitute_term_var_eq, substitute_term_var_eq] at H₁,
  exact H₁ (refl Γ s)
end

def trans {Γ t₁ t₂ t₃} (H : Γ ⊢ t₁ ≍ t₂) (H' : Γ ⊢ t₂ ≍ t₃) : Γ ⊢ t₁ ≍ t₃ :=
begin 
  have H₁ := prf.subst t₂ t₃ (equal (lift_term1 t₁) (var 0)) H', 
  rw [substitute_formula_equal, substitute_formula_equal, substitute_term_lift_term, substitute_term_lift_term, substitute_term_var_eq, substitute_term_var_eq] at H₁,
  exact H₁ H
end

end
end fol
open fol fol.preterm
variable {L : Language}
#check substitute_formula0 (@equal L (var 0) (var 0)) (var 7)
#reduce substitute_formula0 (@equal L (var 0) (var 0)) (var 7)