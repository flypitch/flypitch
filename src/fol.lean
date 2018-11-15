/- A development of first-order logic in Lean.

* The object theory uses classical logic
* We use de Bruijn variables.
* We use a deep embedding of the logic, i.e. the type of terms and formulas is inductively defined.
* There is no well-formedness predicate; all elements of type "term" are well-formed.
-/

import .to_mathlib tactic.squeeze data.quot

open nat set
universe variables u v

local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`:0) := l

namespace fol

/- realizers of variables are just maps ℕ → S. We need some operations on them -/

def subst_realize {S : Type u} (v : ℕ → S) (x : S) (n k : ℕ) : S :=
if k < n then v k else if n < k then v (k - 1) else x

notation v `[`:95 x ` // `:95 n `]`:0 := _root_.fol.subst_realize v x n

@[simp] lemma subst_realize_lt {S : Type u} (v : ℕ → S) (x : S) {n k : ℕ} (H : k < n) : 
  v[x // n] k = v k :=
by simp only [H, subst_realize, if_true, eq_self_iff_true]

@[simp] lemma subst_realize_gt {S : Type u} (v : ℕ → S) (x : S) {n k : ℕ} (H : n < k) : 
  v[x // n] k = v (k-1) :=
have h : ¬(k < n), from lt_asymm H,
by simp only [*, subst_realize, if_true, eq_self_iff_true, if_false]

@[simp] lemma subst_realize_var_eq {S : Type u} (v : ℕ → S) (x : S) (n : ℕ) : v[x // n] n = x :=
by simp only [subst_realize, lt_irrefl, eq_self_iff_true, if_false]

lemma subst_realize_congr {S : Type u} {v v' : ℕ → S} (hv : ∀k, v k = v' k) (x : S) (n k : ℕ) : 
 v [x // n] k = v' [x // n] k :=
by apply lt_by_cases k n; intro h; 
   simp only [*, subst_realize_lt, subst_realize_gt, subst_realize_var_eq, eq_self_iff_true]

lemma subst_realize2 {S : Type u} (v : ℕ → S) (x x' : S) (n₁ n₂ k : ℕ) :
  v [x' // n₁ + n₂] [x // n₁] k = v [x // n₁] [x' // n₁ + n₂ + 1] k :=
begin
    apply lt_by_cases k n₁; intro h,
    { have : k < n₁ + n₂, from lt_of_le_of_lt (k.le_add_right n₂) (add_lt_add_right h n₂),
      have : k < n₁ + n₂ + 1, from lt.step this,
      simp only [*, fol.subst_realize_lt, eq_self_iff_true] },
    { have : k < n₂ + (k + 1), from nat.lt_add_left _ _ n₂ (lt.base k),
      subst h, simp [*, -add_comm] },
    apply lt_by_cases k (n₁ + n₂ + 1); intro h',
    { have : k - 1 < n₁ + n₂, from (nat.sub_lt_right_iff_lt_add (one_le_of_lt h)).2 h', 
      simp [*, -add_comm, -add_assoc] },
    { subst h', simp [h, -add_comm, -add_assoc] },
    { have : n₁ + n₂ < k - 1, from nat.lt_sub_right_of_add_lt h', 
      have : n₁ < k - 1, from lt_of_le_of_lt (n₁.le_add_right n₂) this,
      simp only [*, fol.subst_realize_gt, eq_self_iff_true] }
end

lemma subst_realize2_0 {S : Type u} (v : ℕ → S) (x x' : S) (n k : ℕ) :
  v [x' // n] [x // 0] k = v [x // 0] [x' // n + 1] k :=
let h := subst_realize2 v x x' 0 n k in by simp only [zero_add] at h; exact h

lemma subst_realize_irrel {S : Type u} {v₁ v₂ : ℕ → S} {n : ℕ} (hv : ∀k < n, v₁ k = v₂ k) (x : S)
  {k : ℕ} (hk : k < n + 1) : v₁[x // 0] k = v₂[x // 0] k :=
begin
  cases k, refl, have h : 0 < succ k, from zero_lt_succ k, simp [h, hv k (lt_of_succ_lt_succ hk)]
end

lemma lift_subst_realize_cancel {S : Type u} (v : ℕ → S) (k : ℕ) : 
  (λn, v (n + 1))[v 0 // 0] k = v k :=
begin
  cases k, refl, have h : 0 < succ k, from zero_lt_succ k, simp [h],
end

/- the same operations on maps fin n → S. We need some operations on them -/

-- def subst_fin_realize {S : Type u} {m} (v : fin m → S) (x : S) (n k : fin (m+1)) : S :=
-- if h : k.val < n.val then v ⟨k, lt_of_lt_of_le h $ le_of_lt_succ n.2⟩ else 
-- if h' : n.val < k.val then v ⟨k - 1, (nat.sub_lt_right_iff_lt_add $ one_le_of_lt h').2 k.2⟩ else x

-- notation v `[`:95 x ` // `:95 n `]`:0 := _root_.fol.subst_fin_realize v x n

-- @[simp] lemma subst_fin_realize_lt {S : Type u} {m} (v : fin m → S) (x : S) {n k : fin (m+1)} 
--   (h : k.val < n.val) : v[x // n] k = v ⟨k, lt_of_lt_of_le h $ le_of_lt_succ n.2⟩ :=
-- by simp only [h, subst_fin_realize, dif_pos, eq_self_iff_true]

-- @[simp] lemma subst_fin_realize_gt {S : Type u} {m} (v : fin m → S) (x : S) {n k : fin (m+1)} 
--   (H : n.val < k.val) : 
--   v[x // n] k = v ⟨k - 1, (nat.sub_lt_right_iff_lt_add $ one_le_of_lt H).2 k.2⟩ :=
-- have h : ¬(k.val < n.val), from lt_asymm H,
-- by simp only [*, subst_fin_realize, dif_pos, eq_self_iff_true, dif_neg, not_false_iff]

-- @[simp] lemma subst_fin_realize_var_eq {S : Type u} {m} (v : fin m → S) (x : S) {n k : fin (m+1)}
--   (h : n.val = k.val) : v[x // n] k = x :=
-- by simp only [h, subst_fin_realize, lt_irrefl, eq_self_iff_true, dif_neg, not_false_iff]

-- lemma subst_fin_realize_congr {S : Type u} {m} {v v' : fin m → S} (hv : ∀k, v k = v' k) (x : S) 
--   (n k : fin (m+1)) : v [x // n] k = v' [x // n] k :=
-- by apply lt_by_cases k.val n.val; intro h; simp*

-- lemma subst_fin_realize2 {S : Type u} {m} (v : fin m → S) (x x' : S) (n₁ n₂ : fin m) 
--   (k : fin (m+1)) : v [x' // n₁ + n₂] [x // n₁] k = v [x // n₁] [x' // n₁ + n₂ + 1] k :=
-- begin
--     apply lt_by_cases k n₁; intro h,
--     { have : k < n₁ + n₂, from lt_of_le_of_lt (k.le_add_right n₂) (add_lt_add_right h n₂),
--       have : k < n₁ + n₂ + 1, from lt.step this,
--       simp [*, -add_comm, -add_assoc] },
--     { have : k < n₂ + (k + 1), from nat.lt_add_left _ _ n₂ (lt.base k),
--       subst h, simp [*, -add_comm] },
--     apply lt_by_cases k (n₁ + n₂ + 1); intro h',
--     { have : k - 1 < n₁ + n₂, from (nat.sub_lt_right_iff_lt_add (one_le_of_lt h)).2 h', 
--       simp [*, -add_comm, -add_assoc] },
--     { subst h', simp [h, -add_comm, -add_assoc] },
--     { have : n₁ + n₂ < k - 1, from nat.lt_sub_right_of_add_lt h', 
--       have : n₁ < k - 1, from lt_of_le_of_lt (n₁.le_add_right n₂) this,
--       simp [*, -add_comm, -add_assoc] }
-- end

-- lemma subst_fin_realize2_0 {S : Type u} {m} (v : fin m → S) (x x' : S) (n : fin (m+1)) 
--   (k : fin (m+2)) : v [x' // n] [x // 0] k = v [x // 0] [x' // n.raise] k :=
-- sorry

lemma subst_fin_realize_eq {S : Type u} {n} {v₁ : dvector S n} {v₂ : ℕ → S} 
  (hv : ∀k (hk : k < n), v₁.nth k hk = v₂ k) (x : S) (k : ℕ) (hk : k < n+1) : 
    (x::v₁).nth k hk = v₂[x // 0] k :=
begin
  cases k, refl, 
  have h : 0 < succ k, from zero_lt_succ k, 
  have h' : (0 : fin (n+1)).val < (fin.mk (succ k) hk).val, from h, 
  rw [subst_realize_gt v₂ x h, dvector.nth], apply hv 
end

/- 
  Note: we only work in the bottom universe. If we don't, then when we define the realization of
  formulae in a structure S, we want to send preformula n to 
  S → (S → ... → (S → Prop)...)
  with n occurrences of S. If S : Type u, then this type lives in `Type u` for n ≥ 1 and in Type 0 for n = 0, which is super inconvenient/impossible to work with
-/
structure Language : Type (u+1) := 
(functions : ℕ → Type u) (relations : ℕ → Type u)

def Language.constants (L : Language) := L.functions 0
section
parameter (L : Language.{u})

/- preterm l is a partially applied term. if applied to n terms, it becomes a term.
* Every element of preterm 0 is well typed. 
* We use this encoding to avoid mutual or nested inductive types, since those are not too convenient to work with in Lean. -/
inductive preterm : ℕ → Type u
| var {} : ∀ (k : ℕ), preterm 0
| func : ∀ {l : ℕ} (f : L.functions l), preterm l
| app : ∀ {l : ℕ} (t : preterm (l + 1)) (s : preterm 0), preterm l
export preterm

@[reducible] def term := preterm 0

parameter {L}
prefix `&`:max := _root_.fol.preterm.var

@[simp] def apps : ∀{l}, preterm l → dvector term l → term
| _ t []       := t
| _ t (t'::ts) := apps (app t t') ts

@[simp] lemma apps_zero (t : term) (ts : dvector term 0) : apps t ts = t :=
by cases ts; refl

def term_of_function {l} (f : L.functions l) : arity term term l :=
arity.of_dvector_map $ apps (func f)

/- lift_term_at _ t n m raises variables in t which are at least m by n -/
@[simp] def lift_term_at : ∀ {l}, preterm l → ℕ → ℕ → preterm l
| _ &k          n m := if m ≤ k then &(k+n) else &k
| _ (func f)    n m := func f
| _ (app t₁ t₂) n m := app (lift_term_at t₁ n m) (lift_term_at t₂ n m)

notation t ` ↑' `:90 n ` # `:90 m:90 := _root_.fol.lift_term_at t n m -- input ↑ with \u or \upa

@[reducible] def lift_term {l} (t : preterm l) (n : ℕ) : preterm l := t ↑' n # 0
infix ` ↑ `:100 := _root_.fol.lift_term -- input ↑' with \u or \upa
@[reducible, simp] def lift_term1 {l} (t : preterm l) : preterm l := t ↑ 1

@[simp] lemma lift_term_def {l} (t : preterm l) (n : ℕ) : t ↑' n # 0 = t ↑ n := by refl

lemma lift_term_at_inj : ∀ {l} {t t' : preterm l} {n m : ℕ}, t ↑' n # m = t' ↑' n # m → t = t'
| _ &k &k' n m h := 
  by by_cases h₁ : m ≤ k; by_cases h₂ : m ≤ k'; simp [h₁, h₂] at h;
     congr;[assumption, skip, skip, assumption]; exfalso; try {apply h₁}; 
     try {apply h₂}; subst h; apply le_trans (by assumption) (le_add_right _ _)
| _ &k (func f')            n m h := by by_cases h' : m ≤ k; simp [h'] at h; contradiction
| _ &k (app t₁' t₂')        n m h := by by_cases h' : m ≤ k; simp [h'] at h; contradiction
| _ (func f) &k'            n m h := by by_cases h' : m ≤ k'; simp [h'] at h; contradiction
| _ (func f) (func f')      n m h := h
| _ (func f) (app t₁' t₂')  n m h := by cases h
| _ (app t₁ t₂) &k'         n m h := by by_cases h' : m ≤ k'; simp [h'] at h; contradiction
| _ (app t₁ t₂) (func f')   n m h := by cases h
| _ (app t₁ t₂) (app t₁' t₂') n m h := 
  begin injection h, congr; apply lift_term_at_inj; assumption end

@[simp] lemma lift_term_at_zero : ∀ {l} (t : preterm l) (m : ℕ), t ↑' 0 # m = t
| _ &k          m := by simp
| _ (func f)    m := by refl
| _ (app t₁ t₂) m := by dsimp; congr; apply lift_term_at_zero

@[simp] lemma lift_term_zero {l} (t : preterm l) : t ↑ 0 = t := lift_term_at_zero t 0

/- the following lemmas simplify iterated lifts, depending on the size of m' -/
lemma lift_term_at2_small : ∀ {l} (t : preterm l) (n n') {m m'}, m' ≤ m → 
  (t ↑' n # m) ↑' n' # m' = (t ↑' n' # m') ↑' n # (m + n')
| _ &k          n n' m m' H := 
  begin 
    by_cases h : m ≤ k,
    { have h₁ : m' ≤ k := le_trans H h,
      have h₂ : m' ≤ k + n, from le_trans h₁ (k.le_add_right n),
      simp [*, -add_assoc, -add_comm], simp },
    { have h₁ : ¬m + n' ≤ k + n', from λ h', h (le_of_add_le_add_right h'),
      have h₂ : ¬m + n' ≤ k, from λ h', h₁ (le_trans h' (k.le_add_right n')),
      by_cases h' : m' ≤ k; simp [*, -add_comm, -add_assoc] }
  end
| _ (func f)    n n' m m' H := by refl
| _ (app t₁ t₂) n n' m m' H := 
  begin dsimp; congr1; apply lift_term_at2_small; assumption end

lemma lift_term_at2_medium : ∀ {l} (t : preterm l) {n} (n') {m m'}, m ≤ m' → m' ≤ m+n → 
  (t ↑' n # m) ↑' n' # m' = t ↑' (n+n') # m
| _ &k          n n' m m' H₁ H₂ := 
  begin 
    by_cases h : m ≤ k,
    { have h₁ : m' ≤ k + n, from le_trans H₂ (add_le_add_right h n), simp [*, -add_comm], },
    { have h₁ : ¬m' ≤ k, from λ h', h (le_trans H₁ h'), simp [*, -add_comm, -add_assoc] }
  end
| _ (func f)    n n' m m' H₁ H₂ := by refl
| _ (app t₁ t₂) n n' m m' H₁ H₂ := 
  begin dsimp; congr1; apply lift_term_at2_medium; assumption end

lemma lift_term2_medium {l} (t : preterm l) {n} (n') {m'} (h : m' ≤ n) :
  (t ↑ n) ↑' n' # m' = t ↑ (n+n') :=
lift_term_at2_medium t n' m'.zero_le (by simp*)

lemma lift_term2 {l} (t : preterm l) (n n') : (t ↑ n) ↑ n' = t ↑ (n+n') :=
lift_term2_medium t n' n.zero_le

lemma lift_term_at2_eq {l} (t : preterm l) (n n' m : ℕ) : 
  (t ↑' n # m) ↑' n' # (m+n) = t ↑' (n+n') # m :=
lift_term_at2_medium t n' (m.le_add_right n) (le_refl _)

lemma lift_term_at2_large {l} (t : preterm l) {n} (n') {m m'} (H : m + n ≤ m') : 
  (t ↑' n # m) ↑' n' # m' = (t ↑' n' # (m'-n)) ↑' n # m :=
have H₁ : n ≤ m', from le_trans (n.le_add_left m) H,
have H₂ : m ≤ m' - n, from nat.le_sub_right_of_add_le H,
begin rw fol.lift_term_at2_small t n' n H₂, rw [nat.sub_add_cancel], exact H₁ end

@[simp] lemma lift_term_var0 (n : ℕ) : &0 ↑ n = (&n : term) := 
by have h : 0 ≤ 0 := le_refl 0; rw [←lift_term_def]; simp [h, -lift_term_def]

/- subst_term t s n substitutes s for (&n) and reduces the level of all variables above n by 1 -/
def subst_term : ∀ {l}, preterm l → term → ℕ → preterm l
| _ &k          s n := subst_realize var (s ↑ n) n k
| _ (func f)    s n := func f
| _ (app t₁ t₂) s n := app (subst_term t₁ s n) (subst_term t₂ s n)

notation t `[`:max s ` // `:95 n `]`:0 := _root_.fol.subst_term t s n

@[simp] lemma subst_term_var_lt (s : term) {k n : ℕ} (H : k < n) : &k[s // n] = &k :=
by simp only [H, fol.subst_term, fol.subst_realize_lt, eq_self_iff_true]

@[simp] lemma subst_term_var_gt (s : term) {k n : ℕ} (H : n < k) : &k[s // n] = &(k-1) :=
by simp only [H, fol.subst_term, fol.subst_realize_gt, eq_self_iff_true]

@[simp] lemma subst_term_var_eq (s : term) (n : ℕ) : &n[s // n] = s ↑' n # 0 :=
by simp [subst_term]

lemma subst_term_var0 (s : term) : &0[s // 0] = s := by simp

@[simp] lemma subst_term_func {l} (f : L.functions l) (s : term) (n : ℕ) : 
  (func f)[s // n] = func f :=
by refl

@[simp] lemma subst_term_app {l} (t₁ : preterm (l+1)) (t₂ s : term) (n : ℕ) : 
  (app t₁ t₂)[s // n] = app (t₁[s // n]) (t₂[s // n]) :=
by refl

@[simp] lemma subst_term_apps {l} (t : preterm l) (ts : dvector term l) (s : term) (n : ℕ) : 
  (apps t ts)[s // n] = apps (t[s // n]) (ts.map $ λx, x[s // n]) :=
begin
  induction ts generalizing t, refl, apply ts_ih (app t ts_x)
end

/- the following lemmas simplify first lifting and then substituting, depending on the size
  of the substituted variable -/
lemma lift_at_subst_term_large : ∀{l} (t : preterm l) (s : term) {n₁} (n₂) {m}, m ≤ n₁ →
 (t ↑' n₂ # m)[s // n₁+n₂] = (t [s // n₁]) ↑' n₂ # m
| _ &k          s n₁ n₂ m h :=
  begin
    apply lt_by_cases k n₁; intro h₂,
    { have : k < n₁ + n₂, from lt_of_le_of_lt (k.le_add_right n₂) (by simp*),
      by_cases m ≤ k; simp* },
    { subst h₂, simp [*, lift_term2_medium] },
    { have h₂ : m < k, by apply lt_of_le_of_lt; assumption,
      have : m ≤ k - 1, from nat.le_sub_right_of_add_le (succ_le_of_lt h₂),
      have : m ≤ k, from le_of_lt h₂,
      have : 1 ≤ k, from one_le_of_lt h₂,
      simp [*, nat.add_sub_swap this n₂, -add_assoc, -add_comm] }
  end
| _ (func f)    s n₁ n₂ m h := rfl
| _ (app t₁ t₂) s n₁ n₂ m h := by simp*

lemma lift_subst_term_large {l} (t : preterm l) (s : term) (n₁ n₂) :
  (t ↑ n₂)[s // n₁+n₂] = (t [s // n₁]) ↑ n₂ :=
lift_at_subst_term_large t s n₂ n₁.zero_le

lemma lift_subst_term_large' {l} (t : preterm l) (s : term) (n₁ n₂) :
  (t ↑ n₂)[s // n₂+n₁] = (t [s // n₁]) ↑ n₂ :=
by rw [add_comm]; apply lift_subst_term_large

lemma lift_at_subst_term_medium : ∀{l} (t : preterm l) (s : term) {n₁ n₂ m}, m ≤ n₂ → 
  n₂ ≤ m + n₁ → (t ↑' n₁+1 # m)[s // n₂] = t ↑' n₁ # m
| _ &k          s n₁ n₂ m h₁ h₂ := 
  begin 
    by_cases h : m ≤ k,
    { have h₃ : n₂ < k + (n₁ + 1), from lt_succ_of_le (le_trans h₂ (add_le_add_right h _)), 
      simp [*, add_sub_cancel_right] },
    { have h₃ : k < n₂, from lt_of_lt_of_le (lt_of_not_ge h) h₁, simp* }
  end
| _ (func f)    s n₁ n₂ m h₁ h₂ := rfl
| _ (app t₁ t₂) s n₁ n₂ m h₁ h₂ := by simp*

lemma lift_subst_term_medium {l} (t : preterm l) (s : term) (n₁ n₂) :
  (t ↑ ((n₁ + n₂) + 1))[s // n₁] = t ↑ (n₁ + n₂) :=
lift_at_subst_term_medium t s n₁.zero_le (by rw [zero_add]; exact n₁.le_add_right n₂)

lemma lift_at_subst_term_eq {l} (t : preterm l) (s : term) (n : ℕ) : (t ↑' 1 # n)[s // n] = t :=
begin rw [lift_at_subst_term_medium t s, lift_term_at_zero]; refl end

@[simp] lemma lift_term1_subst_term {l} (t : preterm l) (s : term) : (t ↑ 1)[s // 0] = t :=
lift_at_subst_term_eq t s 0

lemma lift_at_subst_term_small : ∀{l} (t : preterm l) (s : term) (n₁ n₂ m), 
 (t ↑' n₁ # (m + n₂ + 1))[s ↑' n₁ # m // n₂] = (t [s // n₂]) ↑' n₁ # (m + n₂)
| _ &k          s n₁ n₂ m := 
  begin
    by_cases h : m + n₂ + 1 ≤ k,
    { change m + n₂ + 1 ≤ k at h, 
      have h₂ : n₂ < k := lt_of_le_of_lt (le_add_left n₂ m) (lt_of_succ_le h),
      have h₃ : n₂ < k + n₁ := by apply nat.lt_add_right; exact h₂, 
      have h₄ : m + n₂ ≤ k - 1 := nat.le_sub_right_of_add_le h, 
      simp [*, -add_comm, -add_assoc, nat.add_sub_swap (one_le_of_lt h₂)] },
    { change ¬(m + n₂ + 1 ≤ k) at h, 
      apply lt_by_cases k n₂; intro h₂,
      { have h₃ : ¬(m + n₂ ≤ k) := λh', not_le_of_gt h₂ (le_trans (le_add_left n₂ m) h'),
        simp [h, h₂, h₃, -add_comm, -add_assoc] },
      { subst h₂, 
        have h₃ : ¬(k + m + 1 ≤ k) := by rw [add_comm k m]; exact h,
        simp [h, h₃, -add_comm, -add_assoc], 
        exact lift_term_at2_small _ _ _ m.zero_le },
      { have h₃ : ¬(m + n₂ ≤ k - 1) := 
          λh', h $ (nat.le_sub_right_iff_add_le $ one_le_of_lt h₂).mp h',
        simp [h, h₂, h₃, -add_comm, -add_assoc] }}
  end
| _ (func f)    s n₁ n₂ m := rfl
| _ (app t₁ t₂) s n₁ n₂ m := by simp [*, -add_assoc, -add_comm]

lemma subst_term2 : ∀{l} (t : preterm l) (s₁ s₂ : term) (n₁ n₂),
  t [s₁ // n₁] [s₂ // n₁ + n₂] = t [s₂ // n₁ + n₂ + 1] [s₁[s₂ // n₂] // n₁]
| _ &k          s₁ s₂ n₁ n₂ :=
  begin -- can we use subst_realize2 here?
    apply lt_by_cases k n₁; intro h,
    { have : k < n₁ + n₂, from lt_of_le_of_lt (k.le_add_right n₂) (by simp*),
      have : k < n₁ + n₂ + 1, from lt.step this,
      simp only [*, eq_self_iff_true, fol.subst_term_var_lt] },
    { have : k < k + (n₂ + 1), from lt_succ_of_le (le_add_right _ n₂),
      subst h, simp [*, lift_subst_term_large', -add_comm] },
    apply lt_by_cases k (n₁ + n₂ + 1); intro h',
    { have : k - 1 < n₁ + n₂, from (nat.sub_lt_right_iff_lt_add (one_le_of_lt h)).2 h', 
      simp [*, -add_comm, -add_assoc] },
    { subst h', simp [h, lift_subst_term_medium, -add_comm, -add_assoc] },
    { have : n₁ + n₂ < k - 1, from nat.lt_sub_right_of_add_lt h', 
      have : n₁ < k - 1, from lt_of_le_of_lt (n₁.le_add_right n₂) this,
      simp only [*, eq_self_iff_true, fol.subst_term_var_gt] }
  end
| _ (func f)    s₁ s₂ n₁ n₂ := rfl
| _ (app t₁ t₂) s₁ s₂ n₁ n₂ := by simp*

lemma subst_term2_0 {l} (t : preterm l) (s₁ s₂ : term) (n) :
  t [s₁ // 0] [s₂ // n] = t [s₂ // n + 1] [s₁[s₂ // n] // 0] :=
let h := subst_term2 t s₁ s₂ 0 n in by simp only [zero_add] at h; exact h

lemma lift_subst_term_cancel : ∀{l} (t : preterm l) (n : ℕ), (t ↑' 1 # (n+1))[&0 // n] = t
| _ &k          n :=
  begin
    apply lt_by_cases n k; intro h, 
    { change n+1 ≤ k at h, have h' : n < k+1, from lt.step (lt_of_succ_le h), simp [h, h'] }, 
    { have h' : ¬(k+1 ≤ k), from not_succ_le_self k, simp [h, h'] },
    { have h' : ¬(n+1 ≤ k) := not_le_of_lt (lt.step h), simp [h, h'] }
  end
| _ (func f)    n := rfl
| _ (app t₁ t₂) n := by dsimp; simp [*]


/- Probably useful facts about substitution which we should add when needed:
(forall M N i j k, ( M [ j ← N] ) ↑' k # (j+i) = (M ↑' k # (S (j+i))) [ j ← (N ↑' k # i ) ])
subst_travers : (forall M N P n, (M [← N]) [n ← P] = (M [n+1 ← P])[← N[n← P]])
erasure_lem3 : (forall n m t, m>n->#m = (#m ↑' 1 # (S n)) [n ← t]). 
lift_is_lift_sublemma : forall j v, j<v->exists w,#v=w↑1#j. 
lift_is_lift : (forall N A n i j,N ↑' i # n=A ↑' 1 # j -> j<n -> exists M,N=M ↑' 1 # j)
subst_is_lift : (forall N T A n j, N [n ← T]=A↑' 1#j->j<n->exists M,N=M↑' 1#j)
-/

/- preformula l is a partially applied formula. if applied to n terms, it becomes a formula. 
  * We only have implication as binary connective. Since we use classical logic, we can define
    the other connectives from implication and falsum. 
  * Similarly, universal quantification is our only quantifier. 
  * We could make `falsum` and `equal` into elements of rel. However, if we do that, then we cannot make the interpretation of them in a model definitionally what we want.
-/
parameter (L)
inductive preformula : ℕ → Type u
| falsum {} : preformula 0
| equal (t₁ t₂ : term) : preformula 0
| rel {l : ℕ} (R : L.relations l) : preformula l
| apprel {l : ℕ} (f : preformula (l + 1)) (t : term) : preformula l
| imp (f₁ f₂ : preformula 0) : preformula 0
| all (f : preformula 0) : preformula 0
export preformula
@[reducible] def formula := preformula 0
parameter {L}

notation `⊥` := _root_.fol.preformula.falsum -- input: \bot
infix ` ≃ `:88 := _root_.fol.preformula.equal -- input \~- or \simeq
infix ` ⟹ `:62 := _root_.fol.preformula.imp -- input \==>
prefix `∀'`:110 := _root_.fol.preformula.all
def not (f : formula) : formula := imp f ⊥
prefix `∼`:max := _root_.fol.not -- input \~, the ASCII character ~ has too low precedence
def and (f₁ f₂ : formula) : formula := ∼(f₁ ⟹ ∼f₂)
infixr ` ⊓ ` := _root_.fol.and -- input: \sqcap
def or (f₁ f₂ : formula) : formula := ∼f₁ ⟹ f₂
infixr ` ⊔ ` := _root_.fol.or -- input: \sqcup
def biimp (f₁ f₂ : formula) : formula := (f₁ ⟹ f₂) ⊓ (f₂ ⟹ f₁)
infix ` ⇔ `:61 := _root_.fol.biimp -- input \<=>
def ex (f : formula) : formula := ∼ ∀' ∼f
prefix `∃'`:110 := _root_.fol.ex

def apps_rel : ∀{l} (f : preformula l) (ts : dvector term l), formula
| 0     f []      := f
| (n+1) f (t::ts) := apps_rel (apprel f t) ts

@[simp] lemma apps_rel_zero (f : formula) (ts : dvector term 0) : apps_rel f ts = f :=
by cases ts; refl

def formula_of_relation {l} (R : L.relations l) : arity term formula l :=
arity.of_dvector_map $ apps_rel (rel R)

def formula.rec {C : formula → Sort v}
  (hfalsum : C ⊥)
  (hequal : Π (t₁ t₂ : term), C (t₁ ≃ t₂))
  (hrel : Π {l} (R : L.relations l) (ts : dvector term l), C (apps_rel (rel R) ts))
  (himp : Π {{f₁ f₂ : formula}} (ih₁ : C f₁) (ih₂ : C f₂), C (f₁ ⟹ f₂))
  (hall : Π {{f : formula}} (ih : C f), C (∀' f)) : ∀f, C f :=
have h : ∀{l} (f : preformula l) (ts : dvector term l), C (apps_rel f ts),
begin
  intros, induction f; try {rw ts.zero_eq},
  exact hfalsum, apply hequal, apply hrel, apply f_ih (f_t::ts),
  exact himp (f_ih_f₁ ([])) (f_ih_f₂ ([])), exact hall (f_ih ([]))
end,
λ f, h f ([])

@[simp] def lift_formula_at : ∀ {l}, preformula l → ℕ → ℕ → preformula l
| _ falsum       n m := falsum
| _ (t₁ ≃ t₂)    n m := lift_term_at t₁ n m ≃ lift_term_at t₂ n m
| _ (rel R)      n m := rel R
| _ (apprel f t) n m := apprel (lift_formula_at f n m) (lift_term_at t n m)
| _ (f₁ ⟹ f₂)   n m := lift_formula_at f₁ n m ⟹ lift_formula_at f₂ n m
| _ (∀' f)       n m := ∀' lift_formula_at f n (m+1)

notation f ` ↑' `:90 n ` # `:90 m:90 := _root_.fol.lift_formula_at f n m -- input ↑' with \upa

@[reducible] def lift_formula {l} (f : preformula l) (n : ℕ) : preformula l := f ↑' n # 0
infix ` ↑ `:100 := _root_.fol.lift_formula -- input ↑' with \upa
@[reducible, simp] def lift_formula1 {l} (f : preformula l) : preformula l := f ↑ 1

@[simp] lemma lift_formula_def {l} (f : preformula l) (n : ℕ) : f ↑' n # 0 = f ↑ n := by refl
@[simp] lemma lift_formula1_not (n : ℕ) (f : formula) : ∼f ↑ n  = ∼(f ↑ n) := by refl

lemma lift_formula_at_inj {l} {f f' : preformula l} {n m : ℕ} (H : f ↑' n # m = f' ↑' n # m) : 
  f = f' :=
begin
  induction f generalizing m; cases f'; injection H,
  { simp only [lift_term_at_inj h_1, lift_term_at_inj h_2, eq_self_iff_true, and_self] },
  { simp only [f_ih h_1, lift_term_at_inj h_2, eq_self_iff_true, and_self] },
  { simp only [f_ih_f₁ h_1, f_ih_f₂ h_2, eq_self_iff_true, and_self] },
  { simp only [f_ih h_1, eq_self_iff_true] }
end

@[simp] lemma lift_formula_at_zero : ∀ {l} (f : preformula l) (m : ℕ), f ↑' 0 # m = f
| _ falsum       m := by refl
| _ (t₁ ≃ t₂)    m := by simp
| _ (rel R)      m := by refl
| _ (apprel f t) m := by simp; apply lift_formula_at_zero
| _ (f₁ ⟹ f₂)   m := by dsimp; congr1; apply lift_formula_at_zero
| _ (∀' f)       m := by simp; apply lift_formula_at_zero

/- the following lemmas simplify iterated lifts, depending on the size of m' -/
lemma lift_formula_at2_small : ∀ {l} (f : preformula l) (n n') {m m'}, m' ≤ m → 
  (f ↑' n # m) ↑' n' # m' = (f ↑' n' # m') ↑' n # (m + n')
| _ falsum       n n' m m' H := by refl
| _ (t₁ ≃ t₂)    n n' m m' H := by simp [lift_term_at2_small, H]
| _ (rel R)      n n' m m' H := by refl
| _ (apprel f t) n n' m m' H := 
  by simp [lift_term_at2_small, H, -add_comm]; apply lift_formula_at2_small; assumption
| _ (f₁ ⟹ f₂)   n n' m m' H := by dsimp; congr1; apply lift_formula_at2_small; assumption
| _ (∀' f)       n n' m m' H :=
  by simp [lift_term_at2_small, H, lift_formula_at2_small f n n' (add_le_add_right H 1)]

lemma lift_formula_at2_medium : ∀ {l} (f : preformula l) (n n') {m m'}, m ≤ m' → m' ≤ m+n → 
  (f ↑' n # m) ↑' n' # m' = f ↑' (n+n') # m
| _ falsum       n n' m m' H₁ H₂ := by refl
| _ (t₁ ≃ t₂)    n n' m m' H₁ H₂ := by simp [*, lift_term_at2_medium]
| _ (rel R)      n n' m m' H₁ H₂ := by refl
| _ (apprel f t) n n' m m' H₁ H₂ := by simp [*, lift_term_at2_medium, -add_comm]
| _ (f₁ ⟹ f₂)   n n' m m' H₁ H₂ := by simp*
| _ (∀' f)       n n' m m' H₁ H₂ :=
  have m' + 1 ≤ (m + 1) + n, from le_trans (add_le_add_right H₂ 1) (by simp), by simp*

lemma lift_formula_at2_eq {l} (f : preformula l) (n n' m : ℕ) : 
  (f ↑' n # m) ↑' n' # (m+n) = f ↑' (n+n') # m :=
lift_formula_at2_medium f n n' (m.le_add_right n) (le_refl _)

lemma lift_formula_at2_large {l} (f : preformula l) (n n') {m m'} (H : m + n ≤ m') : 
  (f ↑' n # m) ↑' n' # m' = (f ↑' n' # (m'-n)) ↑' n # m :=
have H₁ : n ≤ m', from le_trans (n.le_add_left m) H,
have H₂ : m ≤ m' - n, from nat.le_sub_right_of_add_le H,
begin rw lift_formula_at2_small f n' n H₂, rw [nat.sub_add_cancel], exact H₁ end

@[simp] def subst_formula : ∀ {l}, preformula l → term → ℕ → preformula l
| _ falsum       s n := falsum
| _ (t₁ ≃ t₂)    s n := subst_term t₁ s n ≃ subst_term t₂ s n
| _ (rel R)      s n := rel R
| _ (apprel f t) s n := apprel (subst_formula f s n) (subst_term t s n)
| _ (f₁ ⟹ f₂)   s n := subst_formula f₁ s n ⟹ subst_formula f₂ s n
| _ (∀' f)       s n := ∀' subst_formula f s (n+1)

notation f `[`:95 s ` // `:95 n `]`:0 := _root_.fol.subst_formula f s n

lemma subst_formula_equal (t₁ t₂ s : term) (n : ℕ) :
  (t₁ ≃ t₂)[s // n] = t₁[s // n] ≃ (t₂[s // n]) :=
by refl

@[simp] lemma subst_formula_biimp (f₁ f₂ : formula) (s : term) (n : ℕ) :
  (f₁ ⇔ f₂)[s // n] = f₁[s // n] ⇔ (f₂[s // n]) :=
by refl

@[simp] lemma subst_formula_apps_rel {l} (f : preformula l) (ts : dvector term l) (s : term) 
  (n : ℕ): (apps_rel f ts)[s // n] = apps_rel (f[s // n]) (ts.map $ λx, x[s // n]) :=
begin
  induction ts generalizing f, refl, apply ts_ih (apprel f ts_x)
end

lemma lift_at_subst_formula_large : ∀{l} (f : preformula l) (s : term) {n₁} (n₂) {m}, m ≤ n₁ →
  (f ↑' n₂ # m)[s // n₁+n₂] = (f [s // n₁]) ↑' n₂ # m
| _ falsum       s n₁ n₂ m h := by refl
| _ (t₁ ≃ t₂)    s n₁ n₂ m h := by simp [*, lift_at_subst_term_large]
| _ (rel R)      s n₁ n₂ m h := by refl
| _ (apprel f t) s n₁ n₂ m h := by simp [*, lift_at_subst_term_large]
| _ (f₁ ⟹ f₂)   s n₁ n₂ m h := by simp*
| _ (∀' f)       s n₁ n₂ m h := 
  by have := lift_at_subst_formula_large f s n₂ (add_le_add_right h 1); simp at this; simp*

lemma lift_subst_formula_large {l} (f : preformula l) (s : term) {n₁ n₂} :
  (f ↑ n₂)[s // n₁+n₂] = (f [s // n₁]) ↑ n₂ :=
lift_at_subst_formula_large f s n₂ n₁.zero_le

lemma lift_subst_formula_large' {l} (f : preformula l) (s : term) {n₁ n₂} :
  (f ↑ n₂)[s // n₂+n₁] = (f [s // n₁]) ↑ n₂ :=
by rw [add_comm]; apply lift_subst_formula_large

lemma lift_at_subst_formula_medium : ∀{l} (f : preformula l) (s : term) {n₁ n₂ m}, m ≤ n₂ → 
  n₂ ≤ m + n₁ → (f ↑' n₁+1 # m)[s // n₂] = f ↑' n₁ # m
| _ falsum       s n₁ n₂ m h₁ h₂ := by refl
| _ (t₁ ≃ t₂)    s n₁ n₂ m h₁ h₂ := by simp [*, lift_at_subst_term_medium]
| _ (rel R)      s n₁ n₂ m h₁ h₂ := by refl
| _ (apprel f t) s n₁ n₂ m h₁ h₂ := by simp [*, lift_at_subst_term_medium]
| _ (f₁ ⟹ f₂)   s n₁ n₂ m h₁ h₂ := by simp*
| _ (∀' f)       s n₁ n₂ m h₁ h₂ := 
  begin
    have h : n₂ + 1 ≤ (m + 1) + n₁, from le_trans (add_le_add_right h₂ 1) (by simp),
    have := lift_at_subst_formula_medium f s (add_le_add_right h₁ 1) h, 
    simp only [fol.subst_formula, fol.lift_formula_at] at this, simp*
  end

lemma lift_subst_formula_medium {l} (f : preformula l) (s : term) (n₁ n₂) :
  (f ↑ ((n₁ + n₂) + 1))[s // n₁] = f ↑ (n₁ + n₂) :=
lift_at_subst_formula_medium f s n₁.zero_le (by rw [zero_add]; exact n₁.le_add_right n₂)

lemma lift_at_subst_formula_eq {l} (f : preformula l) (s : term) (n : ℕ) : 
  (f ↑' 1 # n)[s // n] = f :=
begin rw [lift_at_subst_formula_medium f s, lift_formula_at_zero]; refl end

@[simp] lemma lift_formula1_subst {l} (f : preformula l) (s : term) : (f ↑ 1)[s // 0] = f :=
lift_at_subst_formula_eq f s 0

lemma lift_at_subst_formula_small : ∀{l} (f : preformula l) (s : term) (n₁ n₂ m), 
 (f ↑' n₁ # (m + n₂ + 1))[s ↑' n₁ # m // n₂] = (f [s // n₂]) ↑' n₁ # (m + n₂)
| _ falsum       s n₁ n₂ m := by refl
| _ (t₁ ≃ t₂)    s n₁ n₂ m := 
    by dsimp; simp only [lift_at_subst_term_small, eq_self_iff_true, and_self]
| _ (rel R)      s n₁ n₂ m := by refl
| _ (apprel f t) s n₁ n₂ m := 
    by dsimp; simp only [*, lift_at_subst_term_small, eq_self_iff_true, and_self]
| _ (f₁ ⟹ f₂)   s n₁ n₂ m := 
    by dsimp; simp only [*, lift_at_subst_term_small, eq_self_iff_true, and_self]
| _ (∀' f)       s n₁ n₂ m := 
    by have := lift_at_subst_formula_small f s n₁ (n₂+1) m; dsimp; simp at this ⊢; exact this

lemma lift_at_subst_formula_small0 {l} (f : preformula l) (s : term) (n₁ m) :
 (f ↑' n₁ # (m + 1))[s ↑' n₁ # m // 0] = (f [s // 0]) ↑' n₁ # m :=
lift_at_subst_formula_small f s n₁ 0 m

lemma subst_formula2 : ∀{l} (f : preformula l) (s₁ s₂ : term) (n₁ n₂),
  f [s₁ // n₁] [s₂ // n₁ + n₂] = f [s₂ // n₁ + n₂ + 1] [s₁[s₂ // n₂] // n₁]
| _ falsum       s₁ s₂ n₁ n₂ := by refl
| _ (t₁ ≃ t₂)    s₁ s₂ n₁ n₂ := by simp [*, subst_term2]
| _ (rel R)      s₁ s₂ n₁ n₂ := by refl
| _ (apprel f t) s₁ s₂ n₁ n₂ := by simp [*, subst_term2]
| _ (f₁ ⟹ f₂)   s₁ s₂ n₁ n₂ := by simp*
| _ (∀' f)       s₁ s₂ n₁ n₂ := 
  by simp*; rw [add_comm n₂ 1, ←add_assoc, subst_formula2 f s₁ s₂ (n₁ + 1) n₂]; simp

lemma subst_formula2_zero {l} (f : preformula l) (s₁ s₂ : term) (n) :
  f [s₁ // 0] [s₂ // n] = f [s₂ // n + 1] [s₁[s₂ // n] // 0] :=
let h := subst_formula2 f s₁ s₂ 0 n in by simp only [fol.subst_formula, zero_add] at h; exact h

lemma lift_subst_formula_cancel : ∀{l} (f : preformula l) (n : ℕ), (f ↑' 1 # (n+1))[&0 // n] = f
| _ falsum       n := by refl
| _ (t₁ ≃ t₂)    n := by simp [*, lift_subst_term_cancel]
| _ (rel R)      n := by refl
| _ (apprel f t) n := by simp [*, lift_subst_term_cancel]
| _ (f₁ ⟹ f₂)   n := by simp*
| _ (∀' f)       n := by simp*

@[simp] def count_quantifiers : ∀ {l}, preformula l → ℕ
| _ falsum       := 0
| _ (t₁ ≃ t₂)    := 0
| _ (rel R)      := 0
| _ (apprel f t) := 0
| _ (f₁ ⟹ f₂)   := count_quantifiers f₁ + count_quantifiers f₂
| _ (∀' f)       := count_quantifiers f + 1

@[simp] def count_quantifiers_succ {l} (f : preformula (l+1)) : count_quantifiers f = 0 :=
by cases f; refl

@[simp] lemma count_quantifiers_subst : ∀ {l} (f : preformula l) (s : term) (n : ℕ),
  count_quantifiers (f[s // n]) = count_quantifiers f
| _ falsum       s n := by refl
| _ (t₁ ≃ t₂)    s n := by refl
| _ (rel R)      s n := by refl
| _ (apprel f t) s n := by refl
| _ (f₁ ⟹ f₂)   s n := by simp*
| _ (∀' f)       s n := by simp*

/- Provability
* to decide: should Γ be a list or a set (or finset)?
* We use natural deduction as our deduction system, since that is most convenient to work with.
* All rules are motivated to work well with backwards reasoning.
-/
inductive prf : set formula → formula → Type u
| axm     {Γ A} (h : A ∈ Γ) : prf Γ A
| impI    {Γ : set formula} {A B} (h : prf (insert A Γ) B) : prf Γ (A ⟹ B)
| impE    {Γ} (A) {B} (h₁ : prf Γ (A ⟹ B)) (h₂ : prf Γ A) : prf Γ B
| falsumE {Γ : set formula} {A} (h : prf (insert ∼A Γ) falsum) : prf Γ A
| allI    {Γ A} (h : prf (lift_formula1 '' Γ) A) : prf Γ (∀' A)
| allE'   {Γ} A t (h : prf Γ (∀' A)) : prf Γ (A[t // 0])
| refl    (Γ t) : prf Γ (t ≃ t)
| subst'  {Γ} (s t f) (h₁ : prf Γ (s ≃ t)) (h₂ : prf Γ (f[s // 0])) : prf Γ (f[t // 0])

export prf
infix ` ⊢ `:51 := _root_.fol.prf -- input: \|- or \vdash

def provable (T : set formula) (f : formula) := nonempty (prf T f)
infix ` ⊢' `:51 := _root_.fol.provable -- input: \|- or \vdash

def allE {Γ} (A : formula) (t) {B} (H₁ : prf Γ (∀' A)) (H₂ : A[t // 0] = B) : prf Γ B :=
by induction H₂; exact allE' A t H₁

def subst {Γ} {s t} (f₁ : formula) {f₂} (H₁ : prf Γ (s ≃ t)) (H₂ : prf Γ (f₁[s // 0])) 
  (H₃ : f₁[t // 0] = f₂) : prf Γ f₂ :=
by induction H₃; exact subst' s t f₁ H₁ H₂

def axm1 {Γ : set formula} {A : formula} : insert A Γ ⊢ A := by apply axm; left; refl
def axm2 {Γ : set formula} {A B : formula} : insert A (insert B Γ) ⊢ B := 
by apply axm; right; left; refl

def weakening {Γ Δ} {f : formula} (H₁ : Γ ⊆ Δ) (H₂ : Γ ⊢ f) : Δ ⊢ f :=
begin
  induction H₂ generalizing Δ,
  { apply axm, exact H₁ H₂_h, },
  { apply impI, apply H₂_ih, apply insert_subset_insert, apply H₁ },
  { apply impE, apply H₂_ih_h₁, assumption, apply H₂_ih_h₂, assumption },
  { apply falsumE, apply H₂_ih, apply insert_subset_insert, apply H₁ },
  { apply allI, apply H₂_ih, apply image_subset _ H₁ },
  { apply allE', apply H₂_ih, assumption },
  { apply refl },
  { apply subst', apply H₂_ih_h₁, assumption, apply H₂_ih_h₂, assumption },
end

def prf_lift {Γ} {f : formula} (n m : ℕ) (H : Γ ⊢ f) : (λf', f' ↑' n # m) '' Γ ⊢ f ↑' n # m :=
begin
  induction H generalizing m,
  { apply axm, apply mem_image_of_mem _ H_h },
  { apply impI, have h := @H_ih m, rw [image_insert_eq] at h, exact h },
  { apply impE, apply H_ih_h₁, apply H_ih_h₂ },
  { apply falsumE, have h := @H_ih m, rw [image_insert_eq] at h, exact h },
  { apply allI, rw [←image_comp], have h := @H_ih (m+1), rw [←image_comp] at h, 
    apply cast _ h, congr1, apply image_congr', intro f', symmetry,
    exact lift_formula_at2_small f' _ _ m.zero_le },
  { apply allE _ _ (H_ih m), apply lift_at_subst_formula_small0 },
  { apply refl },
  { apply subst _ (H_ih_h₁ m), 
    { have h := @H_ih_h₂ m, rw [←lift_at_subst_formula_small0] at h, exact h},
    rw [lift_at_subst_formula_small0] },
end

def substitution {Γ} {f : formula} {t n} (H : Γ ⊢ f) : (λx, x[t // n]) '' Γ ⊢ f[t // n] :=
begin
  induction H generalizing n,
  { apply axm, apply mem_image_of_mem _ H_h },
  { apply impI, have h := @H_ih n, rw [image_insert_eq] at h, exact h },
  { apply impE, apply H_ih_h₁, apply H_ih_h₂ },
  { apply falsumE, have h := @H_ih n, rw [image_insert_eq] at h, exact h },
  { apply allI, rw [←image_comp], have h := @H_ih (n+1), rw [←image_comp] at h, 
    apply cast _ h, congr1, apply image_congr', intro,
    apply lift_subst_formula_large },
  { apply allE _ _ H_ih, symmetry, apply subst_formula2_zero },
  { apply refl },
  { apply subst _ H_ih_h₁, { have h := @H_ih_h₂ n, rw [subst_formula2_zero] at h, exact h}, 
    rw [subst_formula2_zero] },
end

def weakening1 {Γ} {f₁ f₂ : formula} (H : Γ ⊢ f₂) : insert f₁ Γ ⊢ f₂ :=
weakening (subset_insert f₁ Γ) H

def weakening2 {Γ} {f₁ f₂ f₃ : formula} (H : insert f₁ Γ ⊢ f₂) : insert f₁ (insert f₃ Γ) ⊢ f₂ :=
weakening (insert_subset_insert (subset_insert _ Γ)) H

def deduction {Γ} {A B : formula} (H : Γ ⊢ A ⟹ B) : insert A Γ ⊢ B :=
impE A (weakening1 H) axm1

def exfalso {Γ} {A : formula} (H : Γ ⊢ falsum) : prf Γ A :=
falsumE (weakening1 H)

def notI {Γ} {A : formula} (H : Γ ⊢ A ⟹ falsum) : prf Γ (not A) :=
  by {rw[not], assumption}

def andI {Γ} {f₁ f₂ : formula} (H₁ : Γ ⊢ f₁) (H₂ : Γ ⊢ f₂) : Γ ⊢ f₁ ⊓ f₂ :=
begin 
  apply impI, apply impE f₂,
  { apply impE f₁, apply axm1, exact weakening1 H₁ },
  { exact weakening1 H₂ }
end

def andE1 {Γ f₁} (f₂ : formula) (H : Γ ⊢ f₁ ⊓ f₂) : Γ ⊢ f₁ :=
begin 
  apply falsumE, apply impE _ (weakening1 H), apply impI, apply exfalso,
  apply impE f₁; [apply axm2, apply axm1]
end

def andE2 {Γ} (f₁ : formula) {f₂} (H : Γ ⊢ f₁ ⊓ f₂) : Γ ⊢ f₂ :=
begin apply falsumE, apply impE _ (weakening1 H), apply impI, apply axm2 end

def orI1 {Γ} {A B : formula} (H : Γ ⊢ A) : Γ ⊢ A ⊔ B :=
begin apply impI, apply exfalso, refine impE _ _ (weakening1 H), apply axm1 end

def orI2 {Γ} {A B : formula} (H : Γ ⊢ B) : Γ ⊢ A ⊔ B :=
impI $ weakening1 H

def orE {Γ} {A B C : formula} (H₁ : Γ ⊢ A ⊔ B) (H₂ : insert A Γ ⊢ C) (H₃ : insert B Γ ⊢ C) : 
  Γ ⊢ C :=
begin
  apply falsumE, apply impE C, { apply axm1 },
  apply impE B, { apply impI, exact weakening2 H₃ },
  apply impE _ (weakening1 H₁),
  apply impI (impE _ axm2 (weakening2 H₂))
end

def biimpI {Γ} {f₁ f₂ : formula} (H₁ : insert f₁ Γ ⊢ f₂) (H₂ : insert f₂ Γ ⊢ f₁) : Γ ⊢ f₁ ⇔ f₂ :=
by apply andI; apply impI; assumption

def biimpE1 {Γ} {f₁ f₂ : formula} (H : Γ ⊢ f₁ ⇔ f₂) : insert f₁ Γ ⊢ f₂ := deduction (andE1 _ H)
def biimpE2 {Γ} {f₁ f₂ : formula} (H : Γ ⊢ f₁ ⇔ f₂) : insert f₂ Γ ⊢ f₁ := deduction (andE2 _ H)

lemma iff_of_biimp {Γ} {f₁ f₂ : formula} (H : Γ ⊢' f₁ ⇔ f₂) : Γ ⊢' f₁ ↔ Γ ⊢' f₂ :=
⟨(H.map (andE1 _)).map2 (impE _), (H.map (andE2 _)).map2 (impE _)⟩ 

def exI {Γ f} (t : term) (H : Γ ⊢ f [t // 0]) : Γ ⊢ ∃' f :=
begin
  apply impI, 
  apply impE (f[t // 0]) _ (weakening1 H),
  apply allE' ∼f t axm1,
end

def exE {Γ f₁ f₂} (t : term) (H₁ : Γ ⊢ ∃' f₁) 
  (H₂ : insert f₁ (lift_formula1 '' Γ) ⊢ lift_formula1 f₂) : Γ ⊢ f₂ :=
begin
  apply falsumE, apply impE _ (weakening1 H₁), apply allI, apply impI, 
  rw [image_insert_eq], apply impE _ axm2, apply weakening2 H₂
end

def ex_not_of_not_all {Γ} {f : formula} (H : Γ ⊢ ∼ ∀' f) : Γ ⊢ ∃' ∼ f :=
begin
  apply falsumE, apply impE _ (weakening1 H), apply allI, apply falsumE,
  rw [image_insert_eq], apply impE _ axm2, apply exI &0,
  rw [lift_subst_formula_cancel], exact axm1
end

def not_and_self {Γ : set formula} {f : formula} (H : Γ ⊢ f ⊓ ∼f) : Γ ⊢ ⊥ :=
impE f (andE2 f H) (andE1 ∼f H)

lemma prf_all_iff {Γ : set formula} {f} : Γ ⊢' ∀' f ↔ lift_formula1 '' Γ ⊢' f :=
begin
  split,
  { intro H, rw [←lift_subst_formula_cancel f 0], 
    apply nonempty.map (allE' _ _), apply H.map (prf_lift 1 0) },
  { exact nonempty.map allI }
end

-- def andE1 {Γ f₁} (f₂ : formula) (H : Γ ⊢ f₁ ⊓ f₂) : Γ ⊢ f₁ :=
def symm {Γ} {s t : term} (H : Γ ⊢ s ≃ t) : Γ ⊢ t ≃ s :=
begin 
  apply subst (&0 ≃ s ↑ 1) H; rw [subst_formula_equal, lift_term1_subst_term, subst_term_var0],
  apply refl
end

def trans {Γ} {t₁ t₂ t₃ : term} (H : Γ ⊢ t₁ ≃ t₂) (H' : Γ ⊢ t₂ ≃ t₃) : Γ ⊢ t₁ ≃ t₃ :=
begin 
  apply subst (t₁ ↑ 1 ≃ &0) H'; rw [subst_formula_equal, lift_term1_subst_term, subst_term_var0],
  exact H
end

def congr {Γ} {t₁ t₂ : term} (s : term) (H : Γ ⊢ t₁ ≃ t₂) : Γ ⊢ s[t₁ // 0] ≃ s[t₂ // 0] :=
begin 
  apply subst (s[t₁ // 0] ↑ 1 ≃ s) H, 
  { rw [subst_formula_equal, lift_term1_subst_term], apply refl },
  { rw [subst_formula_equal, lift_term1_subst_term] }
end

def app_congr {Γ} {t₁ t₂ : term} (s : preterm 1) (H : Γ ⊢ t₁ ≃ t₂) : Γ ⊢ app s t₁ ≃ app s t₂ :=
begin 
  have h := congr (app (s ↑ 1) &0) H, simp at h, exact h
end

def apprel_congr {Γ} {t₁ t₂ : term} (f : preformula 1) (H : Γ ⊢ t₁ ≃ t₂)
  (H₂ : Γ ⊢ apprel f t₁) : Γ ⊢ apprel f t₂ :=
begin 
  apply subst (apprel (f ↑ 1) &0) H; simp, exact H₂
end

lemma apprel_congr' {Γ} {t₁ t₂ : term} (f : preformula 1) (H : Γ ⊢ t₁ ≃ t₂) :
  Γ ⊢' apprel f t₁ ↔ Γ ⊢' apprel f t₂ :=
⟨nonempty.map $ apprel_congr f H, nonempty.map $ apprel_congr f $ symm H⟩

def imp_trans {Γ} {f₁ f₂ f₃ : formula} (H₁ : Γ ⊢ f₁ ⟹ f₂) (H₂ : Γ ⊢ f₂ ⟹ f₃) : Γ ⊢ f₁ ⟹ f₃ :=
begin
  apply impI, apply impE _ (weakening1 H₂), apply impE _ (weakening1 H₁) axm1
end

def biimp_refl (Γ : set formula) (f : formula) : Γ ⊢ f ⇔ f :=
by apply biimpI; apply axm1

def biimp_trans {Γ} {f₁ f₂ f₃ : formula} (H₁ : Γ ⊢ f₁ ⇔ f₂) (H₂ : Γ ⊢ f₂ ⇔ f₃) : Γ ⊢ f₁ ⇔ f₃ :=
begin
  apply andI; apply imp_trans, 
  apply andE1 _ H₁, apply andE1 _ H₂, apply andE2 _ H₂, apply andE2 _ H₁
end

def equal_preterms (T : set formula) {l} (t₁ t₂ : preterm l) : Type u :=
∀(ts : dvector term l), T ⊢ apps t₁ ts ≃ apps t₂ ts

def equal_preterms_app {T : set formula} {l} {t t' : preterm (l+1)} {s s' : term} 
  (Ht : equal_preterms T t t') (Hs : T ⊢ s ≃ s') : equal_preterms T (app t s) (app t' s') :=
begin
  intro xs,
  apply trans (Ht (xs.cons s)),
  have h := congr (apps (t' ↑ 1) (&0 :: xs.map lift_term1)) Hs, 
  simp [dvector.map_congr (λt, lift_term1_subst_term t s')] at h,
  exact h
end

@[refl] def equal_preterms_refl (T : set formula) {l} (t : preterm l) : equal_preterms T t t :=
λxs, refl T (apps t xs)

def equiv_preformulae (T : set formula) {l} (f₁ f₂ : preformula l) : Type u :=
∀(ts : dvector term l), T ⊢ apps_rel f₁ ts ⇔ apps_rel f₂ ts

def equiv_preformulae_apprel {T : set formula} {l} {f f' : preformula (l+1)} {s s' : term} 
  (Ht : equiv_preformulae T f f') (Hs : T ⊢ s ≃ s') : 
    equiv_preformulae T (apprel f s) (apprel f' s') :=
begin
  intro xs, 
  apply biimp_trans (Ht (xs.cons s)),
  apply subst (apps_rel (f' ↑ 1) ((s :: xs).map lift_term1) ⇔ 
               apps_rel (f' ↑ 1) (&0 :: xs.map lift_term1)) Hs; 
    simp [dvector.map_congr (λt, lift_term1_subst_term t s')],
  apply biimp_refl, refl
end

@[refl] def equiv_preformulae_refl (T : set formula) {l} (f : preformula l) : 
  equiv_preformulae T f f :=
λxs, biimp_refl T (apps_rel f xs)

/- model theory -/

/- an L-structure is a type S with interpretations of the functions and relations on S -/
parameter (L)
structure Structure :=
(carrier : Type u) 
(fun_map : ∀{n}, L.functions n → dvector carrier n → carrier)
(rel_map : ∀{n}, L.relations n → dvector carrier n → Prop) 
parameter {L}
instance has_coe_Structure : has_coe_to_sort (@_root_.fol.Structure L) :=
⟨Type u, Structure.carrier⟩

/- realization of terms -/
@[simp] def realize_term {S : Structure} (v : ℕ → S) : 
  ∀{l} (t : preterm l) (xs : dvector S l), S.carrier
| _ &k          xs := v k
| _ (func f)    xs := S.fun_map f xs
| _ (app t₁ t₂) xs := realize_term t₁ $ realize_term t₂ ([])::xs

lemma realize_term_congr {S : Structure} {v v' : ℕ → S} (h : ∀n, v n = v' n) : 
  ∀{l} (t : preterm l) (xs : dvector S l), realize_term v t xs = realize_term v' t xs
| _ &k          xs := h k
| _ (func f)    xs := by refl
| _ (app t₁ t₂) xs := by dsimp; rw [realize_term_congr t₁, realize_term_congr t₂]

lemma realize_term_subst {S : Structure} (v : ℕ → S) : ∀{l} (n : ℕ) (t : preterm l) 
  (s : term) (xs : dvector S l), realize_term (v[realize_term v (s ↑ n) ([]) // n]) t xs = realize_term v (t[s // n]) xs
| _ n &k          s [] := 
  by apply lt_by_cases k n; intro h;[simp [h], {subst h; simp}, simp [h]]
| _ n (func f)    s xs := by refl
| _ n (app t₁ t₂) s xs := by dsimp; simp*

lemma realize_term_subst_lift {S : Structure} (v : ℕ → S) (x : S) (m : ℕ) : ∀{l} (t : preterm l)
  (xs : dvector S l), realize_term (v [x // m]) (t ↑' 1 # m) xs = realize_term v t xs
| _ &k          [] := 
  begin 
    by_cases h : m ≤ k, 
    { have : m < k + 1, from lt_succ_of_le h, simp* },
    { have : k < m, from lt_of_not_ge h, simp* }
  end
| _ (func f)    xs := by refl
| _ (app t₁ t₂) xs := by simp*

/- realization of formulas -/
@[simp] def realize_formula {S : Structure} : ∀{l}, (ℕ → S) → preformula l → dvector S l → Prop
| _ v falsum       xs := false
| _ v (t₁ ≃ t₂)    xs := realize_term v t₁ xs = realize_term v t₂ xs
| _ v (rel R)      xs := S.rel_map R xs
| _ v (apprel f t) xs := realize_formula v f $ realize_term v t ([])::xs
| _ v (f₁ ⟹ f₂)   xs := realize_formula v f₁ xs → realize_formula v f₂ xs
| _ v (∀' f)       xs := ∀(x : S), realize_formula (v [x // 0]) f xs

lemma realize_formula_congr {S : Structure} : ∀{l} {v v' : ℕ → S} (h : ∀n, v n = v' n) 
  (f : preformula l) (xs : dvector S l), realize_formula v f xs ↔ realize_formula v' f xs
| _ v v' h falsum       xs := by refl
| _ v v' h (t₁ ≃ t₂)    xs := by simp [realize_term_congr h]
| _ v v' h (rel R)      xs := by refl
| _ v v' h (apprel f t) xs := by simp [realize_term_congr h]; rw [realize_formula_congr h]
| _ v v' h (f₁ ⟹ f₂)   xs := by dsimp; rw [realize_formula_congr h, realize_formula_congr h]
| _ v v' h (∀' f)       xs := 
  by apply forall_congr; intro x; apply realize_formula_congr; intro n; 
     apply subst_realize_congr h

lemma realize_formula_subst {S : Structure} : ∀{l} (v : ℕ → S) (n : ℕ) (f : preformula l) 
  (s : term) (xs : dvector S l), realize_formula (v[realize_term v (s ↑ n) ([]) // n]) f xs ↔ realize_formula v (f[s // n]) xs
| _ v n falsum       s xs := by refl
| _ v n (t₁ ≃ t₂)    s xs := by simp [realize_term_subst]
| _ v n (rel R)      s xs := by refl
| _ v n (apprel f t) s xs := by simp [realize_term_subst]; rw realize_formula_subst
| _ v n (f₁ ⟹ f₂)   s xs := by apply imp_congr; apply realize_formula_subst
| _ v n (∀' f)       s xs := 
  begin 
    apply forall_congr, intro x, rw [←realize_formula_subst], apply realize_formula_congr, 
    intro k, rw [subst_realize2_0, ←realize_term_subst_lift v x 0, lift_term_def, lift_term2]
  end

lemma realize_formula_subst0 {S : Structure} {l} (v : ℕ → S) (f : preformula l) (s : term) (xs : dvector S l) :
  realize_formula (v[realize_term v s ([]) // 0]) f xs ↔ realize_formula v (f[s // 0]) xs :=
by have h := realize_formula_subst v 0 f s; simp at h; exact h xs

lemma realize_formula_subst_lift {S : Structure} : ∀{l} (v : ℕ → S) (x : S) (m : ℕ) 
  (f : preformula l) (xs : dvector S l), realize_formula (v [x // m]) (f ↑' 1 # m) xs = realize_formula v f xs
| _ v x m falsum       xs := by refl
| _ v x m (t₁ ≃ t₂)    xs := by simp [realize_term_subst_lift]
| _ v x m (rel R)      xs := by refl
| _ v x m (apprel f t) xs := by simp [realize_term_subst_lift]; rw realize_formula_subst_lift
| _ v x m (f₁ ⟹ f₂)   xs := by apply imp_eq_congr; apply realize_formula_subst_lift
| _ v x m (∀' f)       xs := 
  begin 
    apply forall_eq_congr, intro x', 
    rw [realize_formula_congr (subst_realize2_0 _ _ _ _), realize_formula_subst_lift]
  end

/- the following definitions of provability and satisfiability are not exactly how you normally define them, since we define it for formulae instead of sentences. If all the formulae happen to be sentences, then these definitions are equivalent to the normal definitions (the realization of closed terms and sentences are independent of the realizer v). 
 -/
def all_prf (T T' : set formula) := ∀{{f}}, f ∈ T' → T ⊢ f
infix ` ⊢ `:51 := _root_.fol.all_prf -- input: |- or \vdash

def satisfied_in (S : Structure) (f : formula) := ∀(v : ℕ → S), realize_formula v f ([])
infix ` ⊨ `:51 := _root_.fol.satisfied_in -- input using \|= or \vDash, but not using \models 

def all_satisfied_in (S : Structure) (T : set formula) := ∀{{f}}, f ∈ T → S ⊨ f
infix ` ⊨ `:51 := _root_.fol.all_satisfied_in -- input using \|= or \vDash, but not using \models 

def satisfied (T : set formula) (f : formula) := 
∀(S : Structure) (v : ℕ → S), (∀f' ∈ T, realize_formula v (f' : formula) ([])) → 
  realize_formula v f ([])

infix ` ⊨ `:51 := _root_.fol.satisfied -- input using \|= or \vDash, but not using \models 

def all_satisfied (T T' : set formula) := ∀{{f}}, f ∈ T' → T ⊨ f
infix ` ⊨ `:51 := _root_.fol.all_satisfied -- input using \|= or \vDash, but not using \models 

def satisfied_in_trans {S : Structure} {T : set formula} {f : formula} (H' : S ⊨ T) (H : T ⊨ f) :
  S ⊨ f :=
λv, H S v $ λf' hf', H' hf' v

def all_satisfied_in_trans  {S : Structure} {T T' : set formula} (H' : S ⊨ T) (H : T ⊨ T') :
  S ⊨ T' :=
λf hf, satisfied_in_trans H' $ H hf

def satisfied_of_mem {T : set formula} {f : formula} (hf : f ∈ T) : T ⊨ f :=
λS v h, h f hf

def all_satisfied_of_subset {T T' : set formula} (h : T' ⊆ T) : T ⊨ T' :=
λf hf, satisfied_of_mem $ h hf

def satisfied_trans {T₁ T₂ : set formula} {f : formula} (H' : T₁ ⊨ T₂) (H : T₂ ⊨ f) : T₁ ⊨ f :=
λS v h, H S v $ λf' hf', H' hf' S v h

def all_satisfied_trans {T₁ T₂ T₃ : set formula} (H' : T₁ ⊨ T₂) (H : T₂ ⊨ T₃) : T₁ ⊨ T₃ :=
λf hf, satisfied_trans H' $ H hf

def sweakening {T T' : set formula} (H : T ⊆ T') {f : formula} (HT : T ⊨ f) : T' ⊨ f :=
λS v h, HT S v $ λf' hf', h f' $ H hf'

/- soundness for a set of formulae -/
lemma formula_soundness {Γ : set formula} {A : formula} (H : Γ ⊢ A) : Γ ⊨ A :=
begin
  intro S, induction H; intros v h,
  { apply h, apply H_h },
  { intro ha, apply H_ih, intros f hf, induction hf, { subst hf, assumption }, apply h f hf },
  { exact H_ih_h₁ v h (H_ih_h₂ v h) },
  { apply classical.by_contradiction, intro ha, 
    apply H_ih v, intros f hf, induction hf, { cases hf, exact ha }, apply h f hf },
  { intro x, apply H_ih, intros f hf, cases (mem_image _ _ _).mp hf with f' hf', induction hf', 
    induction hf'_right, rw [realize_formula_subst_lift v x 0 f'], exact h f' hf'_left },
  { rw [←realize_formula_subst0], apply H_ih v h (realize_term v H_t ([])) },
  { dsimp, refl },
  { have h' := H_ih_h₁ v h, dsimp at h', rw [←realize_formula_subst0, ←h', realize_formula_subst0],
    apply H_ih_h₂ v h },
end

/- sentences and theories -/
inductive term_below (n : ℕ) : ∀{l}, preterm l → Type u
| b_var' (k) (hk : k < n) : term_below &k
| b_func {} {l} (f : L.functions l) : term_below (func f)
| b_app' {l} (t₁ : preterm (l+1)) (t₂ : term) (ht₁ : term_below t₁) (ht₂ : term_below t₂) : 
    term_below (app t₁ t₂)

export term_below 

@[reducible, simp] def b_var {n k : ℕ} (hk : k < n) : term_below n &k := b_var' k hk
@[reducible, simp] def b_app {n l : ℕ} {t₁ : preterm (l+1)} {t₂ : term} (ht₁ : term_below n t₁) 
  (ht₂ : term_below n t₂) : term_below n (app t₁ t₂) := b_app' t₁ t₂ ht₁ ht₂

lemma lift_term_below {n : ℕ} : ∀{l} {t : preterm l} (ht : term_below n t) (n') {m : ℕ}
  (h : n ≤ m), t ↑' n' # m = t
| _ _ (b_var' k hk)          n' m h := 
  have h' : ¬(m ≤ k), from not_le_of_lt (lt_of_lt_of_le hk h), by simp [h']
| _ _ (b_func f)             n' m h := by refl
| _ _ (b_app' t₁ t₂ ht₁ ht₂) n' m h := by simp [lift_term_below ht₁ n' h, lift_term_below ht₂ n' h]

@[simp] def realize_term_below {S : Structure} {n} (v : dvector S n) : 
  ∀{l} {t : preterm l} (ht : term_below n t) (xs : dvector S l), S.carrier
| _ _ (b_var' k hk)          xs := v.nth k hk
| _ _ (b_func f)             xs := S.fun_map f xs
| _ _ (b_app' t₁ t₂ ht₁ ht₂) xs := realize_term_below ht₁ $ realize_term_below ht₂ ([])::xs

lemma realize_term_below_eq {S : Structure} {n} {v₁ : dvector S n} {v₂ : ℕ → S}
  (hv : ∀k (hk : k < n), v₁.nth k hk = v₂ k) : ∀{l} {t : preterm l} (ht : term_below n t)
  (xs : dvector S l), realize_term_below v₁ ht xs = realize_term v₂ t xs
| _ _ (b_var' k hk)          xs := hv k hk
| _ _ (b_func f)             xs := by refl
| _ _ (b_app' t₁ t₂ ht₁ ht₂) xs := by simp [realize_term_below_eq ht₁, realize_term_below_eq ht₂]

lemma realize_term_below_irrel' {S : Structure} {n₀ n n'} {v₁ : dvector S n} 
  {v₂ : dvector S n'} 
  (h : ∀m (hn₀ : m < n₀) (hn : m < n) (hn' : m < n'), v₁.nth m hn = v₂.nth m hn')
  {l} {t : preterm l} (ht : term_below n t) (ht' : term_below n' t) 
  (ht0 : term_below n₀ t) (xs : dvector S l) : 
  realize_term_below v₁ ht xs = realize_term_below v₂ ht' xs :=
begin
  induction ht0; cases ht; cases ht',
  { exact h ht0_k ht0_hk ht_hk ht'_hk },
  { refl },
  { simp [ht0_ih_ht₁ ht_ht₁ ht'_ht₁, ht0_ih_ht₂ ht_ht₂ ht'_ht₂] }
end

lemma realize_term_below_irrel {S : Structure} {n n'} {v₁ : dvector S n} 
  {v₂ : dvector S n'} 
  {l} {t : preterm l} (ht : term_below n t) (ht' : term_below n' t) 
  (ht0 : term_below 0 t) (xs : dvector S l) :
  realize_term_below v₁ ht xs = realize_term_below v₂ ht' xs :=
realize_term_below_irrel' (by intros m hm; exfalso; apply not_lt_zero m hm) ht ht' ht0 xs

@[simp] def term_below_lift {n} (n' m) : ∀{l} {t : preterm l} (ht : term_below n t), 
  term_below (n + n') (t ↑' n' # m)
| _ _ (b_var' k hk)          := 
  begin 
    by_cases h : m ≤ k; simp [h, -add_comm]; apply b_var, 
    { apply add_lt_add_right hk },
    { apply lt_of_lt_of_le hk, apply nat.le_add_right }
  end
| _ _ (b_func f)             := b_func f
| _ _ (b_app' t₁ t₂ ht₁ ht₂) := b_app (term_below_lift ht₁) (term_below_lift ht₂)

def term_below_lift0 {n m l} {t : preterm l} (ht : term_below 0 t) : term_below n (t ↑' n # m) :=
by have := term_below_lift n m ht; rw [zero_add] at this; exact this

def term_below_subst {n n'} : ∀{l} {t : preterm l} (ht : term_below (n+n'+1) t) 
  {s : term} (hs : term_below n' s), term_below (n+n') (t[s // n])
| _ _ (b_var' k hk)          s hs := 
  begin
    apply lt_by_cases n k; intro h; simp [h],
    { apply b_var, apply (nat.sub_lt_right_iff_lt_add (one_le_of_lt h)).2 hk,  },
    { apply term_below_lift k 0 hs },
    { apply b_var, apply lt_add_right, exact h }
  end
| _ _ (b_func f)             s hs := b_func f
| _ _ (b_app' t₁ t₂ ht₁ ht₂) s hs := b_app (term_below_subst ht₁ hs) (term_below_subst ht₂ hs)

def term_below_subst_closed {n l} {t : preterm l} (hf : term_below (n+1) t) 
  {s : term} (hs : term_below 0 s) : term_below n (t[s // n]) :=
term_below_subst (by exact hf) hs

instance subsingleton_term_below (n : ℕ) {l} (t : preterm l) : subsingleton (term_below n t) :=
begin
  constructor, intros h h', induction h generalizing h'; cases h'; try {refl}; congr,
  apply h_ih_ht₁, apply h_ih_ht₂
end

def term_below_of_le : ∀ {l} {t : preterm l} {n m : ℕ}, n ≤ m → term_below n t → term_below m t
| _ _ n m h (b_var' k hk)          := b_var $ lt_of_lt_of_le hk h
| _ _ n m h (b_func f)             := b_func f
| _ _ n m h (b_app' t₁ t₂ ht₁ ht₂) := b_app (term_below_of_le h ht₁) (term_below_of_le h ht₂)

def term_below_of_zero {l} {t : preterm l} {n : ℕ} (ht : term_below 0 t) : term_below n t :=
term_below_of_le n.zero_le ht

parameter (L)
def bounded_preterm (n l) := Σ(t : preterm l), term_below n t
def bounded_term    (n)   := Σ(t : term),      term_below n t
def closed_preterm  (l)   := Σ(t : preterm l), term_below 0 t
def closed_term           := Σ(t : term),      term_below 0 t
parameter {L}

def closed_term.eq {n l} {t₁ t₂ : bounded_preterm n l} (h : t₁.fst = t₂.fst) : t₁ = t₂ :=
sigma.eq h (subsingleton.elim _ _)

-- @[reducible] def closed_term.fst : closed_term → term := sigma.fst

def bounded_term_of_closed_term {l n} (t : closed_preterm l) : bounded_preterm n l :=
⟨t.fst, term_below_of_zero t.snd⟩

def bounded_term_lift1 {l n} (t : bounded_preterm n l) : bounded_preterm (n+1) l :=
⟨t.fst, term_below_of_le (nat.le_add_right n 1) t.snd⟩

def bd_var {n} (k : fin n) : bounded_term n := ⟨&k.val, b_var k.is_lt⟩
prefix `&`:max := _root_.fol.bd_var
def bd_func {n l} (f : L.functions l) : bounded_preterm n l := ⟨func f, b_func f⟩
def bd_const {n} (c : L.constants) : bounded_term n := bd_func c
def bd_app {n l} (t₁ : bounded_preterm n (l+1)) (t₂ : bounded_term n) : bounded_preterm n l := 
⟨app t₁.fst t₂.fst, b_app t₁.snd t₂.snd⟩
def c_func {l} (f : L.functions l) : closed_preterm l := bd_func f
def c_const (c : L.constants) : closed_term := c_func c
def c_app {l} (t₁ : closed_preterm (l+1)) (t₂ : closed_term) : closed_preterm l := bd_app t₁ t₂

@[simp] def bd_apps {n} : ∀{l}, bounded_preterm n l → dvector (bounded_term n) l → bounded_term n
| _ t []       := t
| _ t (t'::ts) := bd_apps (bd_app t t') ts

def c_apps {l} : closed_preterm l → dvector closed_term l → closed_term :=
bd_apps

def bounded_term_of_function {l n} (f : L.functions l) : 
  arity (bounded_term n) (bounded_term n) l :=
arity.of_dvector_map $ bd_apps (bd_func f)

def bounded_preterm.rec {n} {C : Πl, bounded_preterm n l → Sort v}
  (Hvar : Πk, C 0 &k)
  (Hfun : Π {l} (f : L.functions l), C l (bd_func f))
  (Happ : Π {l} {t : bounded_preterm n (l+1)} {s : bounded_term n} (ih_t : C (l+1) t) 
    (ih_s : C 0 s), C l (bd_app t s))
  {{l : ℕ}} (f : bounded_preterm n l) : C l f :=
begin
  induction f with f hf, induction hf,
  { exact Hvar ⟨hf_k, hf_hk⟩ },
  { exact Hfun hf_f },
  { exact @Happ _ ⟨hf_t₁, hf_ht₁⟩ ⟨hf_t₂, hf_ht₂⟩ hf_ih_ht₁ hf_ih_ht₂ }
end

def realize_bounded_term {S : Structure} {n} (v : dvector S n)
  {l} (t : bounded_preterm n l) (xs : dvector S l) : S :=
realize_term_below v t.snd xs

@[reducible] def realize_closed_term (S : Structure) (t : closed_term) : S :=
realize_bounded_term ([]) t ([])

@[simp] lemma realize_bounded_term_bd_app {S : Structure}
  {n l} (t : bounded_preterm n (l+1)) (s : bounded_term n) (xs : dvector S n) 
  (xs' : dvector S l) :
  realize_bounded_term xs (bd_app t s) xs' = 
  realize_bounded_term xs t (realize_bounded_term xs s ([])::xs') :=
by refl

@[simp] lemma realize_closed_term_bd_apps {S : Structure}
  {l} (t : closed_preterm l) (ts : dvector closed_term l) :
  realize_closed_term S (bd_apps t ts) = 
  realize_bounded_term ([]) t (ts.map (λt', realize_bounded_term ([]) t' ([]))) :=
begin
  induction ts generalizing t, refl, apply ts_ih (bd_app t ts_x)
end

def lift_bounded_term_at {n' l} (t : bounded_preterm n' l) (n m : ℕ) : 
  bounded_preterm (n'+n) l :=
⟨t.fst ↑' n # m, term_below_lift n m t.snd⟩
notation t ` ↑' `:90 n ` # `:90 m:90 := _root_.fol.lift_bounded_term_at t n m -- input ↑ with \u or \upa

@[reducible] def lift_bounded_term {n' l} (t : bounded_preterm n' l) (n : ℕ) : 
  bounded_preterm (n'+n) l := 
t ↑' n # 0
infix ` ↑ `:100 := _root_.fol.lift_bounded_term -- input ↑' with \u or \upa
@[reducible, simp] def lift_bounded_term1 {n' l} (t : bounded_preterm n' l) : 
  bounded_preterm (n'+1) l := 
t ↑ 1

def substmax_bounded_term {n l} (t : bounded_preterm (n+1) l) (s : closed_term) :
  bounded_preterm n l :=
⟨t.fst[s.fst // n], term_below_subst_closed t.snd s.snd⟩

def substmax_var_lt {n} (k : fin (n+1)) (s : closed_term) (h : k.1 < n) :
  substmax_bounded_term &k s = &⟨k.1, h⟩ :=
begin
  apply closed_term.eq, simp [substmax_bounded_term, bd_var, h]
end

def substmax_var_eq {n} (k : fin (n+1)) (s : closed_term) (h : k.1 = n) :
  substmax_bounded_term &k s = bounded_term_of_closed_term s :=
begin
  apply closed_term.eq, simp [substmax_bounded_term, bd_var],
  simp [h], dsimp only [lift_term], rw [lift_term_below s.2 _ (le_refl _)], refl
end

-- lemma substmax_bounded_term_bd_apps {n l} (t : bounded_preterm (n+1) l) 
--   (s : closed_term) (ts : dvector (bounded_term (n+1)) l) :
--   substmax_bounded_term (bd_apps t ts) s = 
--   bd_apps (substmax_bounded_term t s) (ts.map $ λt', substmax_bounded_term t' s) :=
-- sorry

lemma realize_bounded_term_bd_apps {S : Structure}
  {n l} (xs : dvector S n) (t : bounded_preterm n l) (ts : dvector (bounded_term n) l) :
  realize_bounded_term xs (bd_apps t ts) ([]) =
  realize_bounded_term xs t (ts.map (λt, realize_bounded_term xs t ([]))) :=
begin
  induction ts generalizing t, refl, apply ts_ih (bd_app t ts_x)
end

/- this is the same as realize_term_below, we should probably have a common generalization of this definition -/
-- @[simp] def substitute_term_below {n n'} (v : dvector (bounded_term n') n) : 
--   ∀{l} {t : preterm l} (ht : term_below n t), bounded_preterm n' l
-- | _ _ (b_var' k hk)          := v.nth k hk
-- | _ _ (b_func f)             := bd_func f
-- | _ _ (b_app' t₁ t₂ ht₁ ht₂) := bd_app (substitute_term_below ht₁) $ substitute_term_below ht₂

-- def substitute_bounded_term {n n' l} (t : bounded_preterm n l) 
--   (v : dvector (bounded_term n') n) : bounded_preterm n' l :=
-- substitute_term_below v t.snd

inductive formula_below : ∀{l}, ℕ → preformula l → Type u
| b_falsum {n} : formula_below n falsum
| b_equal' {n} (t₁ t₂) (ht₁ : term_below n t₁) (ht₂ : term_below n t₂) : 
    formula_below n (t₁ ≃ t₂)
| b_rel {n l} (R : L.relations l) : formula_below n (rel R)
| b_apprel' {n l} (f : preformula (l+1)) (t) (hf : formula_below n f) 
    (ht : term_below n t) : formula_below n (apprel f t)
| b_imp' {n} (f₁ f₂ : formula) (hf₁ : formula_below n f₁) (hf₂ : formula_below n f₂) :
    formula_below n (f₁ ⟹ f₂)
| b_all' {n} (f : formula) (hf : formula_below (n+1) f) : formula_below n (∀' f)
export formula_below

@[reducible, simp] def b_equal {n : ℕ} {t₁ t₂ : term} (ht₁ : term_below n t₁) 
  (ht₂ : term_below n t₂) : formula_below n (t₁ ≃ t₂) := 
b_equal' t₁ t₂ ht₁ ht₂

@[reducible, simp] def b_apprel {n l : ℕ} {f : preformula (l+1)} {t : term} 
  (hf : formula_below n f) (ht : term_below n t) : formula_below n (apprel f t) := 
b_apprel' f t hf ht

@[reducible, simp] def b_imp {n : ℕ} {f g : formula} (hf : formula_below n f) 
  (hg : formula_below n g) : formula_below n (f ⟹ g) := 
b_imp' f g hf hg

@[reducible, simp] def b_all {n : ℕ} {f : formula} (hf : formula_below (n+1) f) : 
  formula_below n (∀' f) := 
b_all' f hf

def b_not {n : ℕ} {f : formula} (hf : formula_below n f)  : formula_below n (∼f) := 
b_imp hf b_falsum

def b_and {n : ℕ} {f g : formula} (hf : formula_below n f) (hg : formula_below n g) : 
  formula_below n (f ⊓ g) :=
b_not (b_imp hf (b_not hg))

def b_biimp {n : ℕ} {f g : formula} (hf : formula_below n f) (hg : formula_below n g) : 
  formula_below n (f ⇔ g) :=
b_and (b_imp hf hg) (b_imp hg hf)

lemma lift_formula_below : ∀{n l} {f : preformula l} (hf : formula_below n f) (n') 
  {m : ℕ} (h : n ≤ m), f ↑' n' # m = f
| n _ _ b_falsum                 n' m h := by refl
| n _ _ (b_equal' t₁ t₂ ht₁ ht₂) n' m h := 
  by simp [lift_term_below ht₁ n' h, lift_term_below ht₂ n' h]
| n _ _ (b_rel R)                n' m h := by refl
| n _ _ (b_apprel' f t hf ht)    n' m h :=
  by simp [lift_term_below ht n' h, lift_formula_below hf n' h]
| n _ _ (b_imp' f₁ f₂ hf₁ hf₂)   n' m h := 
  by simp [lift_formula_below hf₁ n' h, lift_formula_below hf₂ n' h]
| n _ _ (b_all' f hf)            n' m h := by simp [lift_formula_below hf n' (add_le_add_right h 1)]

@[simp] def realize_formula_below {S : Structure} : ∀{n} (v : dvector S n)
  {l} {f : preformula l} (hf : formula_below n f) (xs : dvector S l), Prop
| n v _ _ b_falsum                 xs := false
| n v _ _ (b_equal' t₁ t₂ ht₁ ht₂) xs := realize_term_below v ht₁ xs = realize_term_below v ht₂ xs
| n v _ _ (b_rel R)                xs := S.rel_map R xs
| n v _ _ (b_apprel' f t hf ht)    xs := 
  realize_formula_below v hf $ realize_term_below v ht ([])::xs
| n v _ _ (b_imp' f₁ f₂ hf₁ hf₂)   xs := 
  realize_formula_below v hf₁ xs → realize_formula_below v hf₂ xs
| n v _ _ (b_all' f hf)            xs := ∀(x : S), realize_formula_below (x::v) hf xs

lemma realize_formula_below_eq {S : Structure} : ∀{n} {v₁ : dvector S n} {v₂ : ℕ → S} 
  (hv : ∀k (hk : k < n), v₁.nth k hk = v₂ k) {l} {f : preformula l} (hf : formula_below n f)
  (xs : dvector S l), realize_formula_below v₁ hf xs ↔ realize_formula v₂ f xs
| n v₁ v₂ hv _ _ b_falsum                 xs := by refl
| n v₁ v₂ hv _ _ (b_equal' t₁ t₂ ht₁ ht₂) xs := 
  by simp [realize_term_below_eq hv ht₁, realize_term_below_eq hv ht₂]
| n v₁ v₂ hv _ _ (b_rel R)                xs := by refl
| n v₁ v₂ hv _ _ (b_apprel' f t hf ht)    xs := 
  by simp [realize_term_below_eq hv ht, realize_formula_below_eq hv hf]
| n v₁ v₂ hv _ _ (b_imp' f₁ f₂ hf₁ hf₂)   xs := 
  by apply imp_congr; apply realize_formula_below_eq hv; assumption
| n v₁ v₂ hv _ _ (b_all' f hf)            xs :=
  begin
    apply forall_congr, intro x, apply realize_formula_below_eq _ hf, 
    apply subst_fin_realize_eq hv
  end

def formula_below_lift : ∀{n} (n' m) {l} {f : preformula l} (hf : formula_below n f), 
  formula_below (n + n') (f ↑' n' # m)
| n n' m _ _ b_falsum                 := b_falsum
| n n' m _ _ (b_equal' t₁ t₂ ht₁ ht₂) := 
  b_equal (term_below_lift n' m ht₁) (term_below_lift n' m ht₂)
| n n' m _ _ (b_rel R)                := b_rel R
| n n' m _ _ (b_apprel' f t hf ht)    := 
  b_apprel (formula_below_lift n' m hf) (term_below_lift n' m ht)
| n n' m _ _ (b_imp' f g hf hg)       := 
  b_imp (formula_below_lift n' m hf) (formula_below_lift n' m hg)
| n n' m _ _ (b_all' f hf)            := 
  begin 
    apply b_all, refine cast _ (@formula_below_lift (n+1) n' (m+1) 0 f (cast _ hf));
      simp only [add_comm, add_left_comm, eq_self_iff_true]
  end

def formula_below_subst : ∀{n n' l} {f : preformula l} (hf : formula_below (n+n'+1) f) 
  {s : term} (hs : term_below n' s), formula_below (n+n') (f[s // n])
| n n' _ _ b_falsum                 s hs := b_falsum
| n n' _ _ (b_equal' t₁ t₂ ht₁ ht₂) s hs := 
  b_equal (term_below_subst ht₁ hs) (term_below_subst ht₂ hs)
| n n' _ _ (b_rel R)                s hs := b_rel R
| n n' _ _ (b_apprel' f t hf ht)    s hs := 
  b_apprel (formula_below_subst hf hs) (term_below_subst ht hs)
| n n' _ _ (b_imp' f g hf hg)       s hs := 
  b_imp (formula_below_subst hf hs) (formula_below_subst hg hs)
| n n' _ _ (b_all' f hf)            s hs := 
  begin 
    apply b_all, refine cast _ (@formula_below_subst (n+1) n' _ f (cast _ hf) _ hs);
      simp only [add_comm, add_left_comm],
  end

def formula_below_subst0 {n l} {f : preformula l} (hf : formula_below (n+1) f) 
  {s : term} (hs : term_below n s) : formula_below n (f[s // 0]) :=
by rw [←zero_add (n+1)] at hf; have := formula_below_subst hf hs; simpa only [zero_add]

def formula_below_subst_closed {n l} {f : preformula l} (hf : formula_below (n+1) f) 
  {s : term} (hs : term_below 0 s) : formula_below n (f[s // n]) :=
formula_below_subst (by exact hf) hs

instance subsingleton_formula_below (n : ℕ) {l} (f : preformula l) : 
  subsingleton (formula_below n f) :=
begin
  constructor, intros h h', induction h generalizing h'; cases h'; try {refl}; congr,
  apply h_ih, apply h_ih_hf₁, apply h_ih_hf₂, apply h_ih
end

lemma realize_formula_below_congr {S : Structure} {n} {v₁ v₂ : dvector S n} 
  (hv : v₁ = v₂) {l} {f : preformula l} {f' : preformula l} (h : f = f') (hf : formula_below n f)(hf' : formula_below n f') : realize_formula_below v₁ hf = realize_formula_below v₂ hf' :=
by subst hv; subst h; congr

set_option trace.check true
lemma realize_formula_below_irrel' {S : Structure} {n₀ n n'} {v₁ : dvector S n} 
  {v₂ : dvector S n'} 
  (h : ∀m (hn₀ : m < n₀) (hn : m < n) (hn' : m < n'), v₁.nth m hn = v₂.nth m hn')
  {l} {f : preformula l} (hf : formula_below n f) (hf' : formula_below n' f) 
  (hf0 : formula_below n₀ f) (xs : dvector S l) : 
  realize_formula_below v₁ hf xs ↔ realize_formula_below v₂ hf' xs :=
begin
  induction hf0 generalizing n n' v₁ v₂ h hf hf' xs; cases hf; cases hf',
  { refl },
  { simp [realize_term_below_irrel' h hf_ht₁ hf'_ht₁ hf0_ht₁,
          realize_term_below_irrel' h hf_ht₂ hf'_ht₂ hf0_ht₂] },
  { refl },
  { simp [realize_term_below_irrel' h hf_ht hf'_ht hf0_ht, hf0_ih h hf_hf hf'_hf] },
  { apply imp_congr, apply hf0_ih_hf₁ h, apply hf0_ih_hf₂ h },
  { apply forall_congr, intro x, apply hf0_ih, intros,
    cases m, refl, apply h m (lt_of_succ_lt_succ hn₀) }
end

lemma realize_formula_below_irrel {S : Structure} {n n'} {v₁ : dvector S n} {v₂ : dvector S n'} 
  {l} {f : preformula l} (hf : formula_below n f) (hf' : formula_below n' f) 
  (hf0 : formula_below 0 f) (xs : dvector S l) : realize_formula_below v₁ hf xs ↔ realize_formula_below v₂ hf' xs :=
realize_formula_below_irrel' (by intros m hm; exfalso; apply not_lt_zero m hm) hf hf' hf0 xs

def formula_below_of_le : ∀ {l} {f : preformula l} {n m : ℕ}, 
  n ≤ m → formula_below n f → formula_below m f
| _ _ n m h b_falsum                 := b_falsum
| _ _ n m h (b_equal' t₁ t₂ ht₁ ht₂) := b_equal (term_below_of_le h ht₁) (term_below_of_le h ht₂)
| _ _ n m h (b_rel R)                := b_rel R
| _ _ n m h (b_apprel' f t hf ht)    := b_apprel (formula_below_of_le h hf) (term_below_of_le h ht)
| _ _ n m h (b_imp' f₁ f₂ hf₁ hf₂)   := 
  b_imp (formula_below_of_le h hf₁) (formula_below_of_le h hf₂)
| _ _ n m h (b_all' f hf)            := b_all $ formula_below_of_le (add_le_add_right h 1) hf

def formula_below_of_zero {l} {f : preformula l} {n : ℕ} (hf : formula_below 0 f) : 
  formula_below n f :=
formula_below_of_le n.zero_le hf

parameter (L)
@[reducible] def bounded_preformula (n l : ℕ) := Σ(f : preformula l), formula_below n f
@[reducible] def bounded_formula    (n : ℕ)   := Σ(f : formula),      formula_below n f
@[reducible] def presentence        (l : ℕ)   := Σ(f : preformula l), formula_below 0 f
@[reducible] def sentence                     := Σ(f : formula),      formula_below 0 f
parameter {L}

def sentence.eq {n l} {f₁ f₂ : bounded_preformula n l} (h : f₁.fst = f₂.fst) : f₁ = f₂ :=
sigma.eq h (subsingleton.elim _ _)

-- @[reducible] def sentence.fst : sentence → formula := sigma.fst

def bounded_formula_of_sentence {l n} (f : presentence l) : bounded_preformula n l :=
⟨f.fst, formula_below_of_zero f.snd⟩

def bounded_formula_lift1 {l n} (f : bounded_preformula n l) : bounded_preformula (n+1) l :=
⟨f.fst, formula_below_of_le (nat.le_add_right n 1) f.snd⟩

def bd_falsum {n} : bounded_formula n := ⟨falsum, b_falsum⟩ 
notation `⊥` := _root_.fol.bd_falsum -- input: \bot
@[reducible] def bd_equal {n} (t₁ t₂ : bounded_term n) : bounded_formula n := 
⟨t₁.fst ≃ t₂.fst, b_equal t₁.snd t₂.snd⟩
infix ` ≃ `:88 := _root_.fol.bd_equal -- input \~- or \simeq
def bd_rel {n l} (r : L.relations l) : bounded_preformula n l := ⟨rel r, b_rel r⟩
def bd_apprel {n l} (f : bounded_preformula n (l+1)) (t : bounded_term n) : 
  bounded_preformula n l :=
⟨apprel f.fst t.fst, b_apprel f.snd t.snd⟩
def bd_imp {n} (f₁ f₂ : bounded_formula n) : bounded_formula n := 
⟨f₁.fst ⟹ f₂.fst, b_imp f₁.snd f₂.snd⟩  
infix ` ⟹ `:62 := _root_.fol.bd_imp -- input \==>
def bd_not {n} (f : bounded_formula n) : bounded_formula n := ⟨∼ f.fst, b_not f.snd⟩
prefix `∼`:max := _root_.fol.bd_not -- input \~, the ASCII character ~ has too low precedence
def bd_and {n} (f₁ f₂ : bounded_formula n) : bounded_formula n := ∼(f₁ ⟹ ∼f₂)
infixr ` ⊓ ` := _root_.fol.bd_and -- input: \sqcap
def bd_or {n} (f₁ f₂ : bounded_formula n) : bounded_formula n := ∼f₁ ⟹ f₂
infixr ` ⊔ ` := _root_.fol.bd_or -- input: \sqcup
def bd_biimp {n} (f₁ f₂ : bounded_formula n) : bounded_formula n := (f₁ ⟹ f₂) ⊓ (f₂ ⟹ f₁)
infix ` ⇔ `:61 := _root_.fol.bd_biimp -- input \<=>
def bd_all {n} (f : bounded_formula (n+1)) : bounded_formula n := ⟨∀' f.fst, b_all f.snd⟩
prefix `∀'`:110 := _root_.fol.bd_all
def bd_ex {n} (f : bounded_formula (n+1)) : bounded_formula n := 
∼ (∀' (∼ f))
prefix `∃'`:110 := _root_.fol.bd_ex

def s_falsum : sentence := ⊥
--notation `⊥` := _root_.fol.s_falsum -- input: \bot
def s_equal (t₁ t₂ : closed_term) : sentence := t₁ ≃ t₂
--infix ` ≃ `:88 := _root_.fol.s_equal -- input \~- or \simeq
def s_rel {l} (r : L.relations l) : presentence l := bd_rel r
def s_apprel {l} (f : presentence (l+1)) (t : closed_term) : presentence l := bd_apprel f t
def s_imp (f₁ f₂ : sentence) : sentence := f₁ ⟹ f₂
--infix ` ⟹ `:62 := _root_.fol.s_imp -- input \==>
def s_not (f : sentence) : sentence := ∼f
--prefix `∼`:max := _root_.fol.s_not -- input \~, the ASCII character ~ has too low precedence
def s_and (f₁ f₂ : sentence) : sentence := f₁ ⊓ f₂
-- infixr ` ⊓ ` := _root_.fol.s_and -- input: \sqcap
def s_or (f₁ f₂ : sentence) : sentence := f₁ ⊔ f₂
-- infixr ` ⊔ ` := _root_.fol.s_or -- input: \sqcup
def s_biimp (f₁ f₂ : sentence) : sentence := f₁ ⇔ f₂
-- infix ` ⇔ `:61 := _root_.fol.s_biimp -- input \<=>
def s_all (f : bounded_formula 1) : sentence := ∀' f
def s_ex (f : bounded_formula 1) : sentence := ∃' f

def bd_apps_rel : ∀{n l} (f : bounded_preformula n l) (ts : dvector (bounded_term n) l),
  bounded_formula n
| _ _ f []      := f
| _ _ f (t::ts) := bd_apps_rel (bd_apprel f t) ts

@[simp] lemma bd_apps_rel_zero {n} (f : bounded_formula n) (ts : dvector (bounded_term n) 0) : 
  bd_apps_rel f ts = f :=
by cases ts; refl

@[simp] def s_apps_rel {l} (f : presentence l) (ts : dvector closed_term l) : sentence :=
bd_apps_rel f ts

def bounded_formula_of_relation {l n} (f : L.relations l) : 
  arity (bounded_term n) (bounded_formula n) l :=
arity.of_dvector_map $ bd_apps_rel (bd_rel f)

def bounded_preformula.rec1 {C : Πn l, bounded_preformula (n+1) l → Sort v}
  (H0 : Π {n}, C n 0 ⊥)
  (H1 : Π {n} (t₁ t₂ : bounded_term (n+1)), C n 0 (t₁ ≃ t₂))
  (H2 : Π {n l : ℕ} (R : L.relations l), C n l (bd_rel R))
  (H3 : Π {n l : ℕ} (f : bounded_preformula (n+1) (l + 1)) (t : bounded_term (n+1)) 
    (ih : C n (l + 1) f), C n l (bd_apprel f t))
  (H4 : Π {n} (f₁ f₂ : bounded_formula (n+1)) (ih₁ : C n 0 f₁) (ih₂ : C n 0 f₂), C n 0 (f₁ ⟹ f₂))
  (H5 : Π {n} (f : bounded_formula (n+2)) (ih : C (n+1) 0 f), C n 0 (∀' f)) 
  {{n l : ℕ}} (f : bounded_preformula (n+1) l) : C n l f :=
begin
  induction f with f hf, induction f generalizing n; cases hf,
  apply H0, 
  exact H1 ⟨f_t₁, hf_ht₁⟩ ⟨f_t₂, hf_ht₂⟩, 
  apply H2,
  exact H3 ⟨f_f, hf_hf⟩ ⟨f_t, hf_ht⟩ (f_ih _),
  exact H4 ⟨f_f₁, hf_hf₁⟩ ⟨f_f₂, hf_hf₂⟩ (f_ih_f₁ _) (f_ih_f₂ _), 
  exact H5 ⟨f_f, hf_hf⟩ (f_ih _)
end

def bounded_preformula.rec {C : Πn l, bounded_preformula n l → Sort v}
  (H0 : Π {n}, C n 0 ⊥)
  (H1 : Π {n} (t₁ t₂ : bounded_term n), C n 0 (t₁ ≃ t₂))
  (H2 : Π {n l : ℕ} (R : L.relations l), C n l (bd_rel R))
  (H3 : Π {n l : ℕ} (f : bounded_preformula n (l + 1)) (t : bounded_term n) (ih : C n (l + 1) f), 
    C n l (bd_apprel f t))
  (H4 : Π {n} (f₁ f₂ : bounded_formula n) (ih₁ : C n 0 f₁) (ih₂ : C n 0 f₂), C n 0 (f₁ ⟹ f₂))
  (H5 : Π {n} (f : bounded_formula (n+1)) (ih : C (n+1) 0 f), C n 0 (∀' f)) 
  {{n l : ℕ}} (f : bounded_preformula n l) : C n l f :=
begin
  induction f with f hf, induction hf,
  apply H0, 
  exact H1 ⟨hf_t₁, hf_ht₁⟩ ⟨hf_t₂, hf_ht₂⟩, 
  apply H2,
  exact H3 ⟨hf_f, hf_hf⟩ ⟨hf_t, hf_ht⟩ hf_ih, 
  exact H4 ⟨hf_f₁, hf_hf₁⟩ ⟨hf_f₂, hf_hf₂⟩ hf_ih_hf₁ hf_ih_hf₂, 
  exact H5 ⟨hf_f, hf_hf⟩ hf_ih
end

@[elab_as_eliminator] def bounded_formula.rec1 {C : Πn, bounded_formula (n+1) → Sort v}
  (hfalsum : Π {n}, C n ⊥)
  (hequal : Π {n} (t₁ t₂ : bounded_term (n+1)), C n (t₁ ≃ t₂))
  (hrel : Π {n l : ℕ} (R : L.relations l) (ts : dvector (bounded_term (n+1)) l), 
    C n (bd_apps_rel (bd_rel R) ts))
  (himp : Π {n} {f₁ f₂ : bounded_formula (n+1)} (ih₁ : C n f₁) (ih₂ : C n f₂), C n (f₁ ⟹ f₂))
  (hall : Π {n} {f : bounded_formula (n+2)} (ih : C (n+1) f), C n (∀' f)) 
  {{n : ℕ}} (f : bounded_formula (n+1)) : C n f :=
have h : ∀{n l} (f : bounded_preformula (n+1) l) (ts : dvector (bounded_term (n+1)) l), 
  C n (bd_apps_rel f ts),
begin
  refine bounded_preformula.rec1 _ _ _ _ _ _; intros; try {rw ts.zero_eq},
  apply hfalsum, apply hequal, apply hrel, apply ih (t::ts),
  exact himp (ih₁ ([])) (ih₂ ([])), exact hall (ih ([]))
end,
h f ([])

def bounded_formula.rec {C : Πn, bounded_formula n → Sort v}
  (hfalsum : Π {n}, C n ⊥)
  (hequal : Π {n} (t₁ t₂ : bounded_term n), C n (t₁ ≃ t₂))
  (hrel : Π {n l : ℕ} (R : L.relations l) (ts : dvector (bounded_term n) l), 
    C n (bd_apps_rel (bd_rel R) ts))
  (himp : Π {n} {f₁ f₂ : bounded_formula n} (ih₁ : C n f₁) (ih₂ : C n f₂), C n (f₁ ⟹ f₂))
  (hall : Π {n} {f : bounded_formula (n+1)} (ih : C (n+1) f), C n (∀' f)) 
  {{n : ℕ}} (f : bounded_formula n) : C n f :=
have h : ∀{n l} (f : bounded_preformula n l) (ts : dvector (bounded_term n) l), 
  C n (bd_apps_rel f ts),
begin
  refine bounded_preformula.rec _ _ _ _ _ _; intros; try {rw ts.zero_eq},
  apply hfalsum, apply hequal, apply hrel, apply ih (t::ts),
  exact himp (ih₁ ([])) (ih₂ ([])), exact hall (ih ([]))
end,
h f ([])


def lift_bounded_formula_at {n' l} (f : bounded_preformula n' l) (n m : ℕ) : 
  bounded_preformula (n'+n) l :=
⟨f.fst ↑' n # m, formula_below_lift n m f.snd⟩
notation t ` ↑' `:90 n ` # `:90 m:90 := _root_.fol.lift_bounded_formula_at t n m -- input ↑ with \u or \upa

@[reducible] def lift_bounded_formula {n' l} (f : bounded_preformula n' l) (n : ℕ) : 
  bounded_preformula (n'+n) l := 
f ↑' n # 0
infix ` ↑ `:100 := _root_.fol.lift_bounded_formula -- input ↑' with \u or \upa
@[reducible, simp] def lift_bounded_formula1 {n' l} (f : bounded_preformula n' l) : 
  bounded_preformula (n'+1) l := 
f ↑ 1

def substmax_bounded_formula {n l} (f : bounded_preformula (n+1) l) (t : closed_term) :
  bounded_preformula n l :=
⟨f.fst[t.fst // n], formula_below_subst_closed f.snd t.snd⟩
--notation f `[`:95 t ` // `:95 n `]`:0 := @_root_.fol.substmax_bounded_formula _ n _ f t

lemma substmax_bounded_formula_bd_apps_rel {n l} (f : bounded_preformula (n+1) l) 
  (t : closed_term) (ts : dvector (bounded_term (n+1)) l) :
  substmax_bounded_formula (bd_apps_rel f ts) t = 
  bd_apps_rel (substmax_bounded_formula f t) (ts.map $ λt', substmax_bounded_term t' t) :=
begin
  induction ts generalizing f, refl, apply ts_ih (bd_apprel f ts_x)
end

def subst0_bounded_formula {n l} (f : bounded_preformula (n+1) l) (t : bounded_term n) :
  bounded_preformula n l :=
⟨f.fst[t.fst // 0], formula_below_subst0 f.snd t.snd⟩

notation f `[`:max s ` /0]`:0 := _root_.fol.subst0_bounded_formula f s

@[simp] def substmax_eq_subst0 {l} (f : bounded_preformula 1 l) (t : closed_term) :
  f[t/0] = substmax_bounded_formula f t :=
by refl

def subst0_closed_formula {n l} (f : bounded_preformula (n+1) l) (t : closed_term) :
  bounded_preformula n l :=
f [bounded_term_of_closed_term t/0]

@[simp] def lift_presentence {l} (n m : ℕ) (f : presentence l) : f.fst ↑' n # m = f.fst :=
lift_formula_below f.snd n m.zero_le
@[simp] def lift_sentence (n m : ℕ) (f : sentence) : f.fst ↑' n # m = f.fst :=
lift_presentence n m f
@[simp] def lift_sentence1 (f : sentence) : f.fst ↑ 1 = f.fst :=
lift_presentence 1 0 f

def realize_bounded_formula {S : Structure} {n} (v : dvector S n)
  {l} (f : bounded_preformula n l) (xs : dvector S l) : Prop :=
realize_formula_below v f.snd xs

@[reducible] def realize_sentence (S : Structure) (f : sentence) : Prop :=
realize_bounded_formula ([] : dvector S 0) f ([])

infix ` ⊨ `:51 := _root_.fol.realize_sentence -- input using \|= or \vDash, but not using \models 

/- this is similar to realize_formula_below -/
-- @[simp] def subst_formula_below : ∀ {n n' l} 
--   {f : preformula l} (hf : formula_below n f), arity (bounded_term n') (bounded_preformula n' l) n
-- | n n' _ _ b_falsum                 := arity_constant ⊥
-- | n n' _ _ (b_equal' t₁ t₂ ht₁ ht₂) := sorry
-- | n n' _ _ (b_rel R)                := arity_constant $ bd_rel R
-- | n n' _ _ (b_apprel' f t hf ht)    := sorry
-- | n n' _ _ (b_imp' f₁ f₂ hf₁ hf₂)   := 
--   arity_postcompose2 bd_imp (subst_formula_below hf₁) (subst_formula_below hf₂)
-- | n n' _ _ (b_all' f hf)            := 
--   arity_postcompose bd_all (arity_precompose (subst_formula_below hf &0) lift_bounded_term1)

-- @[simp] def substitute_formula_below : ∀ {n n'} (v : dvector (bounded_term n') n) {l} 
--   {f : preformula l} (hf : formula_below n f), bounded_preformula n' l
-- | n n' v _ _ b_falsum                 := ⊥
-- | n n' v _ _ (b_equal' t₁ t₂ ht₁ ht₂) := substitute_term_below v ht₁ ≃ substitute_term_below v ht₂
-- | n n' v _ _ (b_rel R)                := bd_rel R
-- | n n' v _ _ (b_apprel' f t hf ht)    := 
--   bd_apprel (substitute_formula_below v hf) $ substitute_term_below v ht
-- | n n' v _ _ (b_imp' f₁ f₂ hf₁ hf₂)   := 
--   substitute_formula_below v hf₁ ⟹ substitute_formula_below v hf₂
-- | n n' v _ _ (b_all' f hf)            := 
--   ∀' substitute_formula_below (&0::v.map lift_bounded_term1) hf

-- @[simp] def substitute_bounded_formula {n n' l} (f : bounded_preformula n l) 
--   (v : dvector (bounded_term n') n) : bounded_preformula n' l :=
-- substitute_formula_below v f.snd

-- @[simp] def substitute_bounded_formula : ∀{n} (n') {l} (f : bounded_preformula n l), 
--   arity (bounded_term n') (bounded_preformula n' l) n
-- | 0     n' l f := ⟨f.fst, sorry⟩
-- | (n+1) n' l f := λt, 
--   let h := subst0_bounded_formula f _ in _

  -- λt, arity_postcompose (λf, subst0_bounded_formula f t) (arity_precompose (substitute_bounded_formula (n'+1) _) lift_bounded_term1)

-- @[simp] def substitute_bounded_formula_arity : ∀{n l} (f : bounded_preformula n l), 
--   arity closed_term (presentence l) n
-- | 0     l f := f
-- | (n+1) l f := λt, substitute_bounded_formula_arity $ subst0_closed_formula f t

-- @[simp] def substitute_bounded_formula_arity_congr : ∀{n l} {f f' : bounded_preformula n l}
--   (h : f.fst = f'.fst), substitute_bounded_formula_arity f = substitute_bounded_formula_arity f'
-- | 0     l f f' h := sentence.eq h
-- | (n+1) l f f' h := funext $ λt, substitute_bounded_formula_arity_congr $ 
--   by dsimp [subst0_closed_formula, subst0_bounded_formula]; rw [h]

-- def substitute_bounded_formula {n l} (f : bounded_preformula n l) 
--   (v : dvector closed_term n) : presentence l :=
-- arity_app (substitute_bounded_formula_arity f) v

-- @[simp] def substitute_bounded_formula_congr {n l} {f f' : bounded_preformula n l}
--   (h : f.fst = f'.fst) (v : dvector closed_term n) : 
--   substitute_bounded_formula f v = substitute_bounded_formula f' v :=
-- by unfold substitute_bounded_formula; rw [substitute_bounded_formula_arity_congr h]

-- lemma substitute_bounded_formula_zero' {n l} (f : bounded_preformula n l) 
--   (v : dvector closed_term n) (h : 0 = n) : 
--   (cast (@congr_arg _ _ _ _ (λn, bounded_preformula n l) h.symm) f).fst = 
--   (substitute_bounded_formula f v).fst :=
-- begin
--   induction f with f hf, induction hf; try { induction h },
--   refl,
--   simp [cast], sorry,
--   refl,
--   sorry,
--   simp [cast], congr1, exact hf_ih_hf₁ v rfl, exact hf_ih_hf₂ v rfl, 
--   simp [cast], congr1, sorry
-- end

-- @[simp] lemma substitute_bounded_formula_zero {l} (f : presentence l) 
--   (v : dvector closed_term 0) : substitute_bounded_formula f v = f :=
-- sentence.eq (substitute_bounded_formula_zero' f v rfl).symm

-- @[simp] lemma substitute_bounded_formula_falsum {n} (v : dvector closed_term n) :
--   substitute_bounded_formula (⊥ : bounded_formula n) v = ⊥ :=
-- begin
--   induction v,
--   { simp },
--   { refine eq.trans _ v_ih, refine substitute_bounded_formula_congr _ v_a_1, refl }
-- end

-- @[simp] lemma substitute_bounded_formula_imp {n} (f₁ f₂ : bounded_formula n) 
--   (v : dvector closed_term n) : substitute_bounded_formula (f₁ ⟹ f₂) v = 
--   substitute_bounded_formula f₁ v ⟹ substitute_bounded_formula f₂ v :=
-- begin
--   induction v,
--   { simp },
--   { transitivity substitute_bounded_formula 
--       (subst0_closed_formula f₁ v_a ⟹ subst0_closed_formula f₂ v_a) v_a_1,
--     refine substitute_bounded_formula_congr _ v_a_1, refl,
--     apply v_ih }
-- end

-- @[simp] lemma substitute_bounded_formula_all {n} (f : bounded_formula (n+1)) 
--   (v : dvector closed_term n) : substitute_bounded_formula (∀' f) v = 
--   ∀' _ :=
-- begin
--   induction v,
--   { simp },
--   { transitivity substitute_bounded_formula 
--       (subst0_closed_formula f₁ v_a ⟹ subst0_closed_formula f₂ v_a) v_a_1,
--     refine substitute_bounded_formula_congr _ v_a_1, refl,
--     apply v_ih }
-- end

@[simp] lemma realize_sentence_false {S : Structure} : S ⊨ (⊥ : sentence) ↔ false :=
by refl
@[simp] lemma realize_sentence_imp {S : Structure} {f₁ f₂ : sentence} : 
  S ⊨ f₁ ⟹ f₂ ↔ (S ⊨ f₁ → S ⊨ f₂) :=
by refl
@[simp] lemma realize_sentence_not {S : Structure} {f : sentence} : S ⊨ ∼f ↔ ¬ S ⊨ f :=
by refl
@[simp] lemma realize_sentence_and {S : Structure} {f₁ f₂ : sentence} :
  S ⊨ f₁ ⊓ f₂ ↔ (S ⊨ f₁ ∧ S ⊨ f₂) :=
begin
  have : S ⊨ f₁ ∧ S ⊨ f₂ ↔ ¬(S ⊨ f₁ → ¬ S ⊨ f₂),
    split,
      {intro H, fapply not.intro, tauto},
      {intro H, have := @not.elim _ (S ⊨ f₁) H, finish},
  rw[this], refl
end
-- @[simp] lemma realize_sentence_all {S : Structure} {f : bounded_formula 1} : S ⊨ ∀'f ↔ ∀ x : S, S ⊨ f[x /0] :=
-- begin
--   sorry
-- end

lemma realize_bounded_formula_bd_apps_rel {S : Structure}
  {n l} (xs : dvector S n) (f : bounded_preformula n l) (ts : dvector (bounded_term n) l) :
  realize_bounded_formula xs (bd_apps_rel f ts) ([]) ↔ 
  realize_bounded_formula xs f (ts.map (λt, realize_bounded_term xs t ([]))) :=
begin
  induction ts generalizing f, refl, apply ts_ih (bd_apprel f ts_x)
end

-- lemma realize_sentence_bd_apps_rel' {S : Structure}
--   {l} (f : presentence l) (ts : dvector closed_term l) :
--   S ⊨ bd_apps_rel f ts ↔ realize_bounded_formula ([]) f (ts.map $ realize_closed_term S) :=
-- realize_bounded_formula_bd_apps_rel ([]) f ts

lemma realize_bd_apps_rel {S : Structure}
  {l} (R : L.relations l) (ts : dvector closed_term l) :
  S ⊨ bd_apps_rel (s_rel R) ts ↔ S.rel_map R (ts.map $ realize_closed_term S) :=
by apply realize_bounded_formula_bd_apps_rel ([]) (bd_rel R) ts

lemma realize_sentence_equal {S : Structure} (t₁ t₂ : closed_term) :
  S ⊨ t₁ ≃ t₂ ↔ realize_closed_term S t₁ = realize_closed_term S t₂  :=
by refl

-- lemma realize_sentence_eq {S : Structure} (v : ℕ → S) (f : sentence) : 
--   realize_sentence S f ↔ realize_formula v f.fst ([]) :=
-- realize_formula_below_eq (λk hk, by exfalso; exact not_lt_zero k hk) f.snd _

lemma realize_sentence_iff {S : Structure} (v : ℕ → S) (f : sentence) : 
  realize_sentence S f ↔ realize_formula v f.fst ([]) :=
realize_formula_below_eq (λk hk, by exfalso; exact not_lt_zero k hk) f.snd _

lemma realize_sentence_of_satisfied_in {S : Structure} [HS : nonempty S] {f : sentence} 
  (H : S ⊨ f.fst) : S ⊨ f :=
begin unfreezeI, induction HS with x, exact (realize_sentence_iff (λn, x) f).mpr (H _) end

lemma satisfied_in_of_realize_sentence {S : Structure} {f : sentence} (H : S ⊨ f) : S ⊨ f.fst :=
λv, (realize_sentence_iff v f).mp H

lemma realize_sentence_iff_satisfied_in {S : Structure} [HS : nonempty S] {f : sentence} :
  S ⊨ f ↔ S ⊨ f.fst  :=
⟨satisfied_in_of_realize_sentence, realize_sentence_of_satisfied_in⟩

/- theories -/

parameter (L)
@[reducible] def Theory := set sentence
parameter {L}

@[reducible] def Theory.fst (T : Theory) : set formula := sigma.fst '' T

def sprf (T : Theory) (f : sentence) := T.fst ⊢ f.fst
infix ` ⊢ `:51 := _root_.fol.sprf -- input: \|- or \vdash

def sprovable (T : Theory) (f : sentence) := T.fst ⊢' f.fst
infix ` ⊢' `:51 := _root_.fol.sprovable -- input: \|- or \vdash

def saxm {T : Theory} {A : sentence} (H : A ∈ T) : T ⊢ A := 
by apply axm; apply mem_image_of_mem _ H

def simpI {T : Theory} {A B : sentence} (H : insert A T ⊢ B) : T ⊢ A ⟹ B := 
begin
  apply impI, simp[sprf, Theory.fst, image_insert_eq] at H, assumption
end

@[reducible] lemma fst_commutes_with_imp {T : Theory} (A B : sentence) : (A ⟹ B).fst = A.fst ⟹ B.fst := by refl

def sfalsumE {T : Theory} {A : sentence} (H : insert ∼A T ⊢ s_falsum) : T ⊢ A :=
begin
  apply falsumE, simp[sprf, Theory.fst, image_insert_eq] at H, assumption
end

def snotI {T : Theory} {A : sentence} (H : T ⊢ A ⟹ s_falsum) : T ⊢ (s_not A) :=
begin
  apply notI, simp[sprf, Theory.fst, image_insert_eq] at H, assumption
end

def sandI {T : Theory} {A B : sentence} (H1 : T ⊢ A) (H2 : T ⊢ B) : T ⊢ A ⊓ B :=
andI H1 H2

def snot_and_self {T : Theory} {A : sentence} (H : T ⊢ A ⊓ ∼ A) : T ⊢ s_falsum :=
begin
cases A with A and hA,
fapply not_and_self,
exact A, simp[sprf] at H,
exact H
end

def sprovable_of_provable {T : Theory} {f : sentence} (h : T.fst ⊢ f.fst) : T ⊢ f := h
def provable_of_sprovable {T : Theory} {f : sentence} (h : T ⊢ f) : T.fst ⊢ f.fst := h

-- def sprovable_of_sprovable_lift_at {T : Theory} (n m : ℕ) {f : formula} (h : T.fst ⊢ f ↑' n # m) :
--   T.fst ⊢ f := 
-- sorry

-- def sprovable_of_sprovable_lift {T : Theory} {f : formula} (h : T.fst ⊢ f ↑ 1) : T.fst ⊢ f := 
-- sprovable_of_sprovable_lift_at 1 0 h

def sprovable_lift {T : Theory} {f : formula} (h : T.fst ⊢ f) : T.fst ⊢ f ↑ 1 := 
begin
  have := prf_lift 1 0 h, dsimp [Theory.fst] at this, 
  rw [←image_comp, image_congr' lift_sentence1] at this, exact this
end

def all_sprovable (T T' : Theory) := ∀(f ∈ T'), T ⊢ f
infix ` ⊢ `:51 := _root_.fol.all_sprovable -- input: \|- or \vdash

def all_realize_sentence (S : Structure) (T : Theory) := ∀{{f}}, f ∈ T → S ⊨ f
infix ` ⊨ `:51 := _root_.fol.all_realize_sentence -- input using \|= or \vDash, but not using \models 

def ssatisfied (T : Theory) (f : sentence) := 
∀{{S : Structure}}, nonempty S → S ⊨ T → S ⊨ f

infix ` ⊨ `:51 := _root_.fol.ssatisfied -- input using \|= or \vDash, but not using \models 

def all_ssatisfied (T T' : Theory) := ∀(f ∈ T'), T ⊨ f
infix ` ⊨ `:51 := _root_.fol.all_ssatisfied -- input using \|= or \vDash, but not using \models 

def satisfied_of_ssatisfied {T : Theory} {f : sentence} (H : T ⊨ f) : T.fst ⊨ f.fst :=
begin
  intros S v hT, rw [←realize_sentence_iff], apply H ⟨ v 0 ⟩,
  intros f' hf', rw [realize_sentence_iff v], apply hT, apply mem_image_of_mem _ hf'
end

def ssatisfied_of_satisfied {T : Theory} {f : sentence} (H : T.fst ⊨ f.fst) : T ⊨ f :=
begin
  intros S hS hT, induction hS with s, rw [realize_sentence_iff (λ_, s)], apply H,
  intros f' hf', rcases hf' with ⟨f', ⟨hf', h⟩⟩, induction h, rw [←realize_sentence_iff],
  exact hT hf'
end

def all_satisfied_of_all_ssatisfied {T T' : Theory} (H : T ⊨ T') : T.fst ⊨ T'.fst :=
begin intros f hf, rcases hf with ⟨f, ⟨hf, rfl⟩⟩, apply satisfied_of_ssatisfied (H f hf) end

def all_ssatisfied_of_all_satisfied {T T' : Theory} (H : T.fst ⊨ T'.fst) : T ⊨ T' :=
begin intros f hf, apply ssatisfied_of_satisfied, apply H, exact mem_image_of_mem _ hf end

def satisfied_iff_ssatisfied {T : Theory} {f : sentence} : T ⊨ f ↔ T.fst ⊨ f.fst :=
⟨satisfied_of_ssatisfied, ssatisfied_of_satisfied⟩

def all_satisfied_sentences_iff {T T' : Theory} : T ⊨ T' ↔ T.fst ⊨ T'.fst :=
⟨all_satisfied_of_all_ssatisfied, all_ssatisfied_of_all_satisfied⟩

def ssatisfied_snot {S : Structure} {f : sentence} (hS : ¬(S ⊨ f)) : S ⊨ ∼ f := 
by exact hS

def Model (T : Theory) : Type (u+1) := Σ' (S : Structure), S ⊨ T

lemma soundness {T : Theory} {A : sentence} (H : T ⊢ A) : T ⊨ A :=
ssatisfied_of_satisfied $ formula_soundness H

def is_consistent (T : Theory) := ¬(T ⊢' (⊥ : sentence))

protected def is_consistent.intro {T : Theory} (H : ¬ T ⊢' (⊥ : sentence)) : is_consistent T :=
H

protected def is_consistent.elim {T : Theory} (H : is_consistent T) : ¬ T ⊢' (⊥ : sentence)
| H' := H H'

def is_complete (T : Theory) := 
is_consistent T ∧ ∀(f : sentence), f ∈ T ∨ ∼ f ∈ T

def mem_of_sprf {T : Theory} (H : is_complete T) {f : sentence} (Hf : T ⊢ f) : f ∈ T :=
begin 
  cases H.2 f, exact h, exfalso, apply H.1, constructor, exact impE _ (saxm h) Hf, 
end

def mem_of_sprovable {T : Theory} (H : is_complete T) {f : sentence} (Hf : T ⊢' f) : f ∈ T :=
by destruct Hf; exact mem_of_sprf H

def sprovable_of_sprovable_or {T : Theory} (H : is_complete T) {f₁ f₂ : sentence}
  (H₂ : T ⊢' f₁ ⊔ f₂) : (T ⊢' f₁) ∨ T ⊢' f₂ :=
begin
  cases H.2 f₁ with h h, { left, exact ⟨saxm h⟩ },
  cases H.2 f₂ with h' h', { right, exact ⟨saxm h'⟩ },
  exfalso, destruct H₂, intro H₂, apply H.1, constructor,
  apply orE H₂; refine impE _ _ axm1; apply weakening1; apply axm; 
    [exact mem_image_of_mem _ h, exact mem_image_of_mem _ h']
end

def impI_of_is_complete {T : Theory} (H : is_complete T) {f₁ f₂ : sentence}
  (H₂ : T ⊢' f₁ → T ⊢' f₂) : T ⊢' f₁ ⟹ f₂ :=
begin
  apply nonempty.map impI, cases H.2 f₁, 
  { apply nonempty.map weakening1, apply H₂, exact ⟨saxm h⟩ },
  apply nonempty.map falsumE, apply nonempty.map weakening1,
  apply nonempty.map2 (impE _) (nonempty.map weakening1 ⟨saxm h⟩) ⟨axm1⟩
end

def notI_of_is_complete {T : Theory} (H : is_complete T) {f : sentence}
  (H₂ : ¬T ⊢' f) : T ⊢' ∼f :=
begin
  apply @impI_of_is_complete _ T H f s_falsum,
  intro h, exfalso, exact H₂ h
end

def has_enough_constants (T : Theory) :=
∃(C : Π(f : bounded_formula 1), L.constants), 
∀(f : bounded_formula 1), T ⊢' ∃' f ⟹ f[c_const (C f)/0]

def find_counterexample_of_henkin {T : Theory} (H₁ : is_complete T) (H₂ : has_enough_constants T) 
  (f : bounded_formula 1) (H₃ : ¬ T ⊢' ∀' f) : ∃(t : closed_term), T ⊢' ∼ f[t/0] :=
begin
  induction H₂ with C HC, 
  refine ⟨c_const (C (∼ f)), _⟩,
  apply (HC _).map2 (impE _),
  apply nonempty.map ex_not_of_not_all, exact notI_of_is_complete H₁ H₃
end

section completeness
parameters {T : Theory} (H₁ : is_complete T) (H₂ : has_enough_constants T)
def term_rel (t₁ t₂ : closed_term) : Prop := T ⊢' t₁ ≃ t₂

def term_setoid : setoid closed_term := 
⟨term_rel, λt, ⟨refl _ _⟩, λt t' H, H.map symm, λt₁ t₂ t₃ H₁ H₂, H₁.map2 trans H₂⟩
local attribute [instance] term_setoid

def term_model' : Type u :=
quotient term_setoid
-- set_option pp.all true
-- #print term_setoid
-- set_option trace.class_instances true

def term_model_fun' {l} (t : closed_preterm l) (ts : dvector closed_term l) : term_model' :=
@quotient.mk _ term_setoid $ c_apps t ts

-- def equal_preterms_trans {T : set formula} : ∀{l} {t₁ t₂ t₃ : preterm l} 
--   (h₁₂ : equal_preterms T t₁ t₂) (h₂₃ : equal_preterms T t₂ t₃), equal_preterms T t₁ t₃ 

def term_model_fun_eq {l} (t t' : closed_preterm (l+1)) (x x' : closed_term)
  (Ht : equal_preterms T.fst t.fst t'.fst) (Hx : T ⊢ x ≃ x') (ts : dvector closed_term l) : 
  term_model_fun' (c_app t x) ts = term_model_fun' (c_app t' x') ts :=
begin
  induction ts generalizing x x',
  { apply quotient.sound, refine ⟨trans (app_congr t.fst Hx) _⟩, apply Ht ([x'.fst]) }, 
  { apply ts_ih, apply equal_preterms_app Ht Hx, apply refl }
end

def term_model_fun {l} (t : closed_preterm l) (ts : dvector term_model' l) : term_model' :=
begin
  refine ts.quotient_lift (term_model_fun' t) _, clear ts,
  intros ts ts' hts,
  induction hts,
  { refl },
  { apply (hts_ih _).trans, induction hts_hx with h, apply term_model_fun_eq,
    refl, exact h }
end

def term_model_rel' {l} (f : presentence l) (ts : dvector closed_term l) : Prop :=
T ⊢' s_apps_rel f ts

def term_model_rel_iff {l} (f f' : presentence (l+1)) (x x' : closed_term)
  (Ht : equiv_preformulae T.fst f.fst f'.fst) (Hx : T ⊢ x ≃ x') (ts : dvector closed_term l) : 
  term_model_rel' (s_apprel f x) ts ↔ term_model_rel' (s_apprel f' x') ts :=
begin
  induction ts generalizing x x',
  { apply iff.trans (apprel_congr' f.fst Hx), 
    apply iff_of_biimp, have := Ht ([x'.fst]), exact ⟨this⟩ }, 
  { apply ts_ih, apply equiv_preformulae_apprel Ht Hx, apply refl }
end

def term_model_rel {l} (f : presentence l) (ts : dvector term_model' l) : Prop :=
begin
  refine ts.quotient_lift (term_model_rel' f) _, exact T, clear ts,
  intros ts ts' hts,
  induction hts,
  { refl },
  { apply (hts_ih _).trans, induction hts_hx with h, apply propext, apply term_model_rel_iff,
    refl, exact h }
end

def term_model : Structure :=
⟨term_model', 
 λn, term_model_fun ∘ c_func, 
 λn, term_model_rel ∘ s_rel⟩

@[reducible] def term_mk : closed_term → term_model :=
@quotient.mk _ term_setoid

-- lemma realize_bounded_preterm_term_model {l n} (ts : dvector closed_term l) 
--   (t : bounded_preterm l n) (ts' : dvector closed_term n) :
--   realize_bounded_term (ts.map term_mk) t (ts'.map term_mk) = 
--   (term_mk _) :=
-- begin
--   induction t with t ht,
--   sorry
-- end

-- dsimp [term_model, Structure.rel_map, term_model_rel], 
--     rw [ts.map_congr realize_closed_term_term_model, dvector.quotient_beta], refl

lemma realize_closed_preterm_term_model {l} (ts : dvector closed_term l) (t : closed_preterm l) : 
  realize_bounded_term ([]) t (ts.map term_mk) = (term_mk (bd_apps t ts)) :=
begin
  revert l t, refine bounded_preterm.rec _ _ _; intros,
  { apply k.fin_zero_elim },
  { apply dvector.quotient_beta },
  { rw [realize_bounded_term_bd_app],
    have := ih_s ([]), dsimp at this, rw this, clear this,
    apply ih_t (s::ts) }
end

@[simp] lemma realize_closed_term_term_model (t : closed_term) :
  realize_closed_term term_model t = term_mk t :=
by apply realize_closed_preterm_term_model ([]) t

lemma realize_subst_preterm {S : Structure} {n l} (t : bounded_preterm (n+1) l)
  (xs : dvector S l) (s : closed_term) (v : dvector S n) :
  realize_bounded_term v (substmax_bounded_term t s) xs =
  realize_bounded_term (v.concat (realize_closed_term S s)) t xs :=
begin
  induction t with t ht, induction t generalizing n; cases ht,
  { by_cases h : t < n,
    { have := substmax_var_lt ⟨t, ht_hk⟩ s h, dsimp [bd_var] at this, rw this, clear this,
      dsimp [substmax_bounded_term, term_below_subst_closed, realize_bounded_term],
      simp only [dvector.map_nth, dvector.concat_nth _ _ _ _ h] },
    { have h' := le_antisymm (le_of_lt_succ ht_hk) (le_of_not_gt h), subst h',
      have := substmax_var_eq ⟨t, ht_hk⟩ s rfl, dsimp [bd_var] at this, rw this, clear this, 
      dsimp [substmax_bounded_term, term_below_subst_closed, realize_bounded_term],
      simp only [dvector.map_nth, dvector.concat_nth_last], 
      dsimp [realize_closed_term, realize_bounded_term],
      cases xs, apply realize_term_below_irrel _ _ s.snd }},
  { refl }, 
  { dsimp [substmax_bounded_term, term_below_subst_closed, term_below_subst, 
      realize_bounded_term], 
    apply _root_.congr, { apply funext, intro xs, apply t_ih_t },
    congr1, apply t_ih_s ([]) }
end

lemma realize_subst_term {S : Structure} {n} (v : dvector S n) (s : closed_term) 
  (t : bounded_term (n+1))  :
  realize_bounded_term v (substmax_bounded_term t s) ([]) =
  realize_bounded_term (v.concat (realize_closed_term S s)) t ([]) :=
by apply realize_subst_preterm t ([]) s v

lemma realize_subst_formula (S : Structure) {n} (f : bounded_formula (n+1))
  (t : closed_term) (v : dvector S n) :
  realize_bounded_formula v (substmax_bounded_formula f t) ([]) ↔
  realize_bounded_formula (v.concat (realize_closed_term S t)) f ([]) :=
begin
  revert n f v, refine bounded_formula.rec1 _ _ _ _ _; intros,
  { simp [realize_bounded_formula, substmax_bounded_formula, bd_falsum], exact λh, h },
  { apply eq.congr, exact realize_subst_term v t t₁, exact realize_subst_term v t t₂ },
  { rw [substmax_bounded_formula_bd_apps_rel, realize_bounded_formula_bd_apps_rel, 
        realize_bounded_formula_bd_apps_rel], 
    simp [dvector.map, -dvector.map_concat], simp only [ts.map_congr (realize_subst_term _ _)],
    apply realize_formula_below_irrel, apply b_rel }, 
  { apply imp_congr, apply ih₁ v, apply ih₂ v },
  { apply forall_congr, intro x, apply ih (x::v) }
end

lemma realize_subst_formula0 (S : Structure) (f : bounded_formula 1) (t : closed_term) :
  S ⊨ f[t/0] ↔ realize_bounded_formula ([realize_closed_term S t]) f ([]) :=
by apply realize_subst_formula S f t ([])

lemma term_model_subst0 (f : bounded_formula 1) (t : closed_term) :
  term_model ⊨ f[t/0] ↔ realize_bounded_formula ([term_mk t]) f ([]) :=
(realize_subst_formula0 term_model f t).trans (by simp)

include H₂
instance nonempty_term_model : nonempty term_model :=
begin
  induction H₂ with C, exact ⟨term_mk (c_const (C (&0 ≃ &0)))⟩
end

include H₁
def term_model_ssatisfied_iff : ∀{n l} (f : presentence l) 
  (ts : dvector closed_term l) (h : count_quantifiers f.fst < n),
  T ⊢' s_apps_rel f ts ↔ term_model ⊨ s_apps_rel f ts :=
begin
  intro n, refine nat.strong_induction_on n _, clear n,
  intros n n_ih l f ts hn,
  induction f with f hf, induction f; cases hf; simp,
  { refine iff.trans _ realize_sentence_false.symm, simp, exact H₁.1.elim },
  { refine iff.trans _ (realize_sentence_equal ⟨f_t₁, hf_ht₁⟩ ⟨f_t₂, hf_ht₂⟩).symm, 
    simp [term_mk], refl },
  { refine iff.trans _ (realize_bd_apps_rel _ _).symm, 
    dsimp [term_model, term_model_rel], 
    rw [ts.map_congr realize_closed_term_term_model, dvector.quotient_beta], refl },
  { apply f_ih (⟨f_t, hf_ht⟩::ts) hf_hf, simp at hn ⊢, exact hn },
  { have ih₁ := f_ih_f₁ ([]) hf_hf₁ (lt_of_le_of_lt (nat.le_add_right _ _) hn),
    have ih₂ := f_ih_f₂ ([]) hf_hf₂ (lt_of_le_of_lt (nat.le_add_left _ _) hn),
    split; intro h,
    { intro h₁, apply ih₂.mp, apply h.map2 (impE _), refine ih₁.mpr h₁ },
    { change term_model ⊨ sigma.mk f_f₁ hf_hf₁ ⟹ sigma.mk f_f₂ hf_hf₂ at h,
      simp at h, simp at ih₁, rw [←ih₁] at h, simp at ih₂, rw [←ih₂] at h,
      exact impI_of_is_complete H₁ h }},
  { split; intro h,
    { apply quotient.ind, intro t, 
      apply (term_model_subst0 ⟨f_f, hf_hf⟩ t).mp,
      cases n with n, { exfalso, exact not_lt_zero _ hn },
      refine (n_ih n (lt.base n) (⟨f_f, hf_hf⟩[t/0]) ([]) _).mp (h.map (allE' _ _)),
      dsimp [subst0_bounded_formula], rw [count_quantifiers_subst], 
      exact lt_of_succ_lt_succ hn },
    { apply classical.by_contradiction, intro H,
      cases find_counterexample_of_henkin H₁ H₂ ⟨f_f, hf_hf⟩ H with t ht,
      apply H₁.left, apply ht.map2 (impE _),
      cases n with n, { exfalso, exact not_lt_zero _ hn },
      refine (n_ih n (lt.base n) (⟨f_f, hf_hf⟩[t/0]) ([]) _).mpr _,
      { dsimp [subst0_bounded_formula], rw [count_quantifiers_subst], exact lt_of_succ_lt_succ hn },
      exact (term_model_subst0 ⟨f_f, hf_hf⟩ t).mpr (h (term_mk t)) }},
end

def term_model_ssatisfied : term_model ⊨ T :=
begin
  intros f hf, apply (term_model_ssatisfied_iff H₁ H₂ f ([]) (lt.base _)).mp, exact ⟨saxm hf⟩
end

-- completeness for complete theories with enough constants
lemma completeness' {f : sentence} (H : T ⊨ f) : T ⊢' f :=
begin
  apply (term_model_ssatisfied_iff H₁ H₂ f ([]) (lt.base _)).mpr,
  apply H, exact fol.nonempty_term_model, 
  apply term_model_ssatisfied H₁ H₂,
end

end completeness

def Th (S : Structure) : Theory := { f : sentence | S ⊨ f }

lemma realize_sentence_Th (S : Structure) : S ⊨ Th S :=
λf hf, hf

lemma is_complete_Th (S : Structure) (HS : nonempty S) : is_complete (Th S) :=
⟨λH, by cases H; apply soundness H HS (realize_sentence_Th S), λ(f : sentence), classical.em (S ⊨ f)⟩

/- maybe define 
presburger_arithmetic := Th (Z,+,0)
true_arithmetic := (ℕ, +, ⬝, 0, 1)
-/

end

end fol
