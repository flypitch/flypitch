namespace tactic
namespace interactive
meta def congr1 : tactic unit := congr_core
end interactive
end tactic

structure Language := 
(relations : Π n : nat, Type) (functions : Π  n : nat, Type)
section
parameter L : Language

/- preterm n is a partially applied term. if applied to n terms, it becomes a term -/
inductive preterm : ℕ → Type 
| var : ℕ → preterm 0
| func : ∀ {n : nat}, L.functions n → preterm n
| apply : ∀ {n : nat}, preterm (n + 1) → preterm 0 → preterm n
open preterm
def term := preterm 0

/- lift_term _ t n m raises variables in t which are at least m by n -/
@[simp] def lift_term : ∀ {l}, preterm l → ℕ → ℕ → preterm l
| _ (var L k)     n m := if m ≤ k then var (k+n) else var k
| _ (func f)      n m := func f
| _ (apply t1 t2) n m := apply (lift_term t1 n m) (lift_term t2 n m)

local notation [parsing_only] t ` ↑ `:55 n ` # `:55 m:55 := lift_term t n m

lemma lift_term_inj : ∀ {l} {t t' : preterm l} {n m : ℕ}, t ↑ n # m = t' ↑ n # m → t = t'
| _ (var L k) (var .(L) k')   n m h := 
  by by_cases h₁ : m ≤ k; by_cases h₂ : m ≤ k'; simp [h₁, h₂] at h; congr; 
       [exact add_right_cancel h, skip, skip, assumption]; exfalso; 
       try {apply h₁}; try {apply h₂}; subst h; 
       apply le_trans (by assumption) (nat.le_add_right _ _)
| _ (var L k) (func f')       n m h := by by_cases h' : m ≤ k; simp [h'] at h; contradiction
| _ (var L k) (apply t1' t2') n m h := by by_cases h' : m ≤ k; simp [h'] at h; contradiction
| _ (func f) (var .(L) k')    n m h := by by_cases h' : m ≤ k'; simp [h'] at h; contradiction
| _ (func f) (func f')        n m h := h
| _ (func f) (apply t1' t2')  n m h := by cases h
| _ (apply t1 t2) (var _ k')  n m h := by by_cases h' : m ≤ k'; simp [h'] at h; contradiction
| _ (apply t1 t2) (func f')   n m h := by cases h
| _ (apply t1 t2) (apply t1' t2') n m h := 
  begin injection h, congr; apply lift_term_inj; assumption end

@[simp] lemma lift_term_zero : ∀ {l} (t : preterm l) (m : ℕ), t ↑ 0 # m = t
| _ (var L k)     m := by simp
| _ (func f)      m := by refl
| _ (apply t1 t2) m := by dsimp; congr; apply lift_term_zero

/- the following lemmas simplify iterated lifts, depending on the size of m' -/
lemma lift_term2_small : ∀ {l} (t : preterm l) (n n') {m m'}, m' ≤ m → 
  (t ↑ n # m) ↑ n' # m' = (t ↑ n' # m') ↑ n # (m + n')
| _ (var L k)     n n' m m' H := 
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
  begin dsimp; congr1; apply lift_term2_small; assumption end

lemma lift_term2_medium : ∀ {l} (t : preterm l) (n n') {m m'}, m ≤ m' → m' ≤ m+n → 
  (t ↑ n # m) ↑ n' # m' = t ↑ (n+n') # m
| _ (var L k)     n n' m m' H₁ H₂ := 
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
  begin dsimp; congr1; apply lift_term2_medium; assumption end

lemma lift_term2_eq {l} (t : preterm l) (n n' m : ℕ) : 
  (t ↑ n # m) ↑ n' # (m+n) = t ↑ (n+n') # m :=
lift_term2_medium t n n' (m.le_add_right n) (le_refl _)

lemma lift_term2_large {l} (t : preterm l) (n n') {m m'} (H : m' ≥ m + n) : 
  (t ↑ n # m) ↑ n' # m' = (t ↑ n' # m'-n) ↑ n # m :=
have H₁ : n ≤ m', from le_trans (n.le_add_left m) H,
have H₂ : m ≤ m' - n, by rw [←nat.add_sub_cancel m n]; apply nat.sub_le_sub_right; exact H,
begin rw lift_term2_small t n' n H₂, rw [nat.sub_add_cancel], exact H₁ end

/- substitute_term t s n substitutes s for (var n) and reduces the level of all variables above n by 1 -/
@[simp] def substitute_term : ∀ {l}, preterm l → term → ℕ → preterm l
| _ (var L k)     s n := if k < n then var k else if k > n then var (k-1) else s
| _ (func f)      s n := func f
| _ (apply t1 t2) s n := apply (substitute_term t1 s n) (substitute_term t2 s n)

/- preformula n is a partially applied formula. if applied to n terms, it becomes a formula -/
inductive preformula : ℕ → Type 
| false : preformula 0
| equal : term → term → preformula 0
| rel : ∀ {n : nat}, L.relations n → preformula n
| apprel : ∀ {n : nat}, preformula (n + 1) → term → preformula n
| imp : preformula 0 → preformula 0 → preformula 0
| all : preformula 0 → preformula 0
open preformula
def formula := preformula 0

@[simp] def lift_formula : ∀ {l}, preformula l → ℕ → ℕ → preformula l
| _ (false L)     n m := false
| _ (equal t1 t2) n m := equal (lift_term t1 n m) (lift_term t2 n m)
| _ (rel R)       n m := rel R
| _ (apprel f t)  n m := apprel (lift_formula f n m) (lift_term t n m)
| _ (imp f1 f2)   n m := imp (lift_formula f1 n m) (lift_formula f2 n m)
| _ (all f)       n m := all (lift_formula f n (m+1))

local notation [parsing_only] f ` ↑ `:55 n ` # `:55 m:55 := lift_formula f n m

@[simp] lemma lift_formula_zero : ∀ {l} (f : preformula l) (m : ℕ), f ↑ 0 # m = f
| _ (false L)     m := by refl
| _ (equal t1 t2) m := by simp
| _ (rel R)       m := by refl
| _ (apprel f t)  m := by simp; apply lift_formula_zero
| _ (imp f1 f2)   m := by dsimp; congr1; apply lift_formula_zero
| _ (all f)       m := by simp; apply lift_formula_zero

/- the following lemmas simplify iterated lifts, depending on the size of m' -/
lemma lift_formula2_small : ∀ {l} (f : preformula l) (n n') {m m'}, m' ≤ m → 
  (f ↑ n # m) ↑ n' # m' = (f ↑ n' # m') ↑ n # (m + n')
| _ (false L)     n n' m m' H := by refl
| _ (equal t1 t2) n n' m m' H := by simp [lift_term2_small, H]
| _ (rel R)       n n' m m' H := by refl
| _ (apprel f t)  n n' m m' H := 
  by simp [lift_term2_small, H, -add_comm]; apply lift_formula2_small; assumption
| _ (imp f1 f2)   n n' m m' H := by dsimp; congr1; apply lift_formula2_small; assumption
| _ (all f)       n n' m m' H :=
  by simp [lift_term2_small, H, lift_formula2_small f n n' (add_le_add_right H 1)]

lemma lift_formula2_medium : ∀ {l} (f : preformula l) (n n') {m m'}, m ≤ m' → m' ≤ m+n → 
  (f ↑ n # m) ↑ n' # m' = f ↑ (n+n') # m
| _ (false L)     n n' m m' H₁ H₂ := by refl
| _ (equal t1 t2) n n' m m' H₁ H₂ := by simp [lift_term2_medium, H₁, H₂]
| _ (rel R)       n n' m m' H₁ H₂ := by refl
| _ (apprel f t)  n n' m m' H₁ H₂ :=
  by simp [lift_term2_medium, H₁, H₂, -add_comm]; apply lift_formula2_medium; assumption
| _ (imp f1 f2)   n n' m m' H₁ H₂ := by dsimp; congr1; apply lift_formula2_medium; assumption
| _ (all f)       n n' m m' H₁ H₂ :=
  have m' + 1 ≤ (m + 1) + n, from le_trans (add_le_add_right H₂ 1) (by simp),
  by simp [lift_term2_medium, H₁, H₂, lift_formula2_medium f n n' (add_le_add_right H₁ 1) this]

lemma lift_formula2_eq {l} (f : preformula l) (n n' m : ℕ) : 
  (f ↑ n # m) ↑ n' # (m+n) = f ↑ (n+n') # m :=
lift_formula2_medium f n n' (m.le_add_right n) (le_refl _)

lemma lift_formula2_large {l} (f : preformula l) (n n') {m m'} (H : m' ≥ m + n) : 
  (f ↑ n # m) ↑ n' # m' = (f ↑ n' # m'-n) ↑ n # m :=
have H₁ : n ≤ m', from le_trans (n.le_add_left m) H,
have H₂ : m ≤ m' - n, by rw [←nat.add_sub_cancel m n]; apply nat.sub_le_sub_right; exact H,
begin rw lift_formula2_small f n' n H₂, rw [nat.sub_add_cancel], exact H₁ end

@[simp] def substitute_formula : ∀ {l}, preformula l → term → ℕ → preformula l
| _ (false L)     s n := false
| _ (equal t1 t2) s n := equal (substitute_term t1 s n) (substitute_term t2 s n)
| _ (rel R)       s n := rel R
| _ (apprel f t)  s n := apprel (substitute_formula f s n) (substitute_term t s n)
| _ (imp f1 f2)   s n := imp (substitute_formula f1 s n) (substitute_formula f2 s n)
| _ (all f)       s n := all (substitute_formula f s (n+1))


end