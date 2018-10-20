/- A development of first-order logic in Lean.

* The object theory uses classical logic
* We use de Bruijn variables.
* We use a deep embedding of the logic, i.e. the type of terms and formulas is inductively defined.
* There is no well-formedness predicate; all elements of type "term" are well-formed.
-/

-- this file depends on mathlib
import data.list.basic algebra.ordered_group data.vector2

universe variables u v w


namespace list
protected def to_set {α : Type u} (l : list α) : set α := { x | x ∈ l }

lemma to_set_map {α : Type u} {β : Type v} (f : α → β) (l : list α) : 
  (l.map f).to_set = f '' l.to_set :=
by apply set.ext; intro b; simp [list.to_set]

lemma exists_of_to_set_subset_image {α : Type u} {β : Type v} {f : α → β} {l : list β} 
  {t : set α} (h : l.to_set ⊆ f '' t) : ∃(l' : list α), map f l' = l :=
begin
  induction l,
  { existsi nil, refl },
  { rcases h (mem_cons_self _ _) with ⟨x, hx, rfl⟩,
    rcases l_ih (λx hx, h $ mem_cons_of_mem _ hx) with ⟨xs, hxs⟩, 
    existsi x::xs, simp* }
end

end list

inductive dvector (α : Type u) : ℕ → Type u
| nil {} : dvector 0
| cons : ∀{n}, α → dvector n → dvector (n+1)

local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

namespace dvector
variables {α : Type u} {β : Type v} {γ : Type w} {n : ℕ}

@[simp] protected def map (f : α → β) : ∀{n : ℕ}, dvector α n → dvector β n
| _ []      := []
| _ (x::xs) := f x :: map xs

@[simp] protected def map_id : ∀{n : ℕ} (xs : dvector α n), xs.map (λx, x) = xs
| _ []      := rfl
| _ (x::xs) := by dsimp; simp*

@[simp] protected def map_congr {f g : α → β} (h : ∀x, f x = g x) : 
  ∀{n : ℕ} (xs : dvector α n), xs.map f = xs.map g
| _ []      := rfl
| _ (x::xs) := by dsimp; simp*

@[simp] protected def map_map (g : β → γ) (f : α → β): ∀{n : ℕ} (xs : dvector α n), 
  (xs.map f).map g = xs.map (λx, g (f x))
  | _ []      := rfl
  | _ (x::xs) := by dsimp; simp*

end dvector

namespace nat
lemma add_sub_swap {n k : ℕ} (h : k ≤ n) (m : ℕ) : n + m - k = n - k + m :=
by rw [add_comm, nat.add_sub_assoc h, add_comm]

lemma one_le_of_lt {n k : ℕ} (H : n < k) : 1 ≤ k :=
succ_le_of_lt (lt_of_le_of_lt n.zero_le H)

lemma add_sub_cancel_right (n m k : ℕ) : n + (m + k) - k = n + m :=
by rw [nat.add_sub_assoc, nat.add_sub_cancel]; apply k.le_add_left

protected lemma pred_lt_iff_lt_succ {m n : ℕ} (H : 1 ≤ m) : pred m < n ↔ m < succ n :=
nat.sub_lt_right_iff_lt_add H

end nat

lemma lt_by_cases {α : Type u} [linear_order α] (x y : α) {P : Prop}
  (h₁ : x < y → P) (h₂ : x = y → P) (h₃ : y < x → P) : P :=
or.elim (lt_trichotomy x y) h₁ (λh, or.elim h h₂ h₃)

lemma imp_eq_congr {a b c d : Prop} (h₁ : a = b) (h₂ : c = d) : (a → c) = (b → d) :=
by subst h₁; subst h₂; refl

lemma forall_eq_congr {α : Sort u} {p q : α → Prop} (h : ∀ a, p a = q a) : 
  (∀ a, p a) = ∀ a, q a :=
have h' : p = q, from funext h, by subst h'; refl

namespace set

-- generalizes set.image_preimage_eq
lemma image_preimage_eq_of_subset_image {α : Type u} {β : Type v} {f : α → β} {s : set β} 
  {t : set α} (h : s ⊆ f '' t) : f '' (f ⁻¹' s) = s :=
subset.antisymm
  (image_preimage_subset f s)
  (λ x hx, begin rcases h hx with ⟨a, ha, rfl⟩, apply mem_image_of_mem f, exact hx end)

end set
open nat set

namespace fin

  def fin_zero_elim {α : fin 0 → Sort u} : ∀(x : fin 0), α x
  | ⟨n, hn⟩ := false.elim (nat.not_lt_zero n hn)
  
end fin

namespace tactic
namespace interactive
meta def congr1 : tactic unit := 
do focus1 (congr_core >> all_goals (try reflexivity >> try assumption))
end interactive
end tactic

namespace fol

/- realizers of variables are just maps ℕ → S. We need some operations on them -/

def subst_realize {S : Type u} (v : ℕ → S) (x : S) (n k : ℕ) : S :=
if k < n then v k else if n < k then v (k - 1) else x

notation v `[`:95 x ` // `:95 n `]`:0 := _root_.fol.subst_realize v x n

@[simp] lemma subst_realize_lt {S : Type u} (v : ℕ → S) (x : S) {n k : ℕ} (H : k < n) : 
  v[x // n] k = v k :=
by simp [H, subst_realize]

@[simp] lemma subst_realize_gt {S : Type u} (v : ℕ → S) (x : S) {n k : ℕ} (H : n < k) : 
  v[x // n] k = v (k-1) :=
have h : ¬(k < n), from lt_asymm H,
by simp [*, subst_realize]

@[simp] lemma subst_realize_var_eq {S : Type u} (v : ℕ → S) (x : S) (n : ℕ) : v[x // n] n = x :=
by simp [subst_realize, lt_irrefl]

lemma subst_realize_congr {S : Type u} {v v' : ℕ → S} (hv : ∀k, v k = v' k) (x : S) (n k : ℕ) : 
 v [x // n] k = v' [x // n] k :=
by apply lt_by_cases k n; intro h; simp*

lemma subst_realize2 {S : Type u} (v : ℕ → S) (x x' : S) (n₁ n₂ k : ℕ) :
  v [x' // n₁ + n₂] [x // n₁] k = v [x // n₁] [x' // n₁ + n₂ + 1] k :=
begin
    apply lt_by_cases k n₁; intro h,
    { have : k < n₁ + n₂, from lt_of_le_of_lt (k.le_add_right n₂) (add_lt_add_right h n₂),
      have : k < n₁ + n₂ + 1, from lt.step this,
      simp [*, -add_comm, -add_assoc] },
    { have : k < n₂ + (k + 1), from nat.lt_add_left _ _ n₂ (lt.base k),
      subst h, simp [*, -add_comm] },
    apply lt_by_cases k (n₁ + n₂ + 1); intro h',
    { have : k - 1 < n₁ + n₂, from (nat.sub_lt_right_iff_lt_add (one_le_of_lt h)).2 h', 
      simp [*, -add_comm, -add_assoc] },
    { subst h', simp [h, -add_comm, -add_assoc] },
    { have : n₁ + n₂ < k - 1, from nat.lt_sub_right_of_add_lt h', 
      have : n₁ < k - 1, from lt_of_le_of_lt (n₁.le_add_right n₂) this,
      simp [*, -add_comm, -add_assoc] }
end

lemma subst_realize2_0 {S : Type u} (v : ℕ → S) (x x' : S) (n k : ℕ) :
  v [x' // n] [x // 0] k = v [x // 0] [x' // n + 1] k :=
let h := subst_realize2 v x x' 0 n k in by simp at h; exact h

lemma subst_realize_irrel {S : Type u} {v₁ v₂ : ℕ → S} {n : ℕ} (hv : ∀k < n, v₁ k = v₂ k) (x : S)
  {k : ℕ} (hk : k < n + 1) : v₁[x // 0] k = v₂[x // 0] k :=
begin
  cases k, refl, have h : 0 < succ k, from zero_lt_succ k, simp [h, hv k (lt_of_succ_lt_succ hk)]
end

/- the same operations on maps fin n → S. We need some operations on them -/

def subst_fin_realize {S : Type u} {m} (v : fin m → S) (x : S) (n k : fin (m+1)) : S :=
if h : k.val < n.val then v ⟨k, lt_of_lt_of_le h $ le_of_lt_succ n.2⟩ else 
if h' : n.val < k.val then v ⟨k - 1, (nat.sub_lt_right_iff_lt_add $ one_le_of_lt h').2 k.2⟩ else x

notation v `[`:95 x ` // `:95 n `]`:0 := _root_.fol.subst_fin_realize v x n

@[simp] lemma subst_fin_realize_lt {S : Type u} {m} (v : fin m → S) (x : S) {n k : fin (m+1)} 
  (h : k.val < n.val) : v[x // n] k = v ⟨k, lt_of_lt_of_le h $ le_of_lt_succ n.2⟩ :=
by simp [h, subst_fin_realize]

@[simp] lemma subst_fin_realize_gt {S : Type u} {m} (v : fin m → S) (x : S) {n k : fin (m+1)} 
  (H : n.val < k.val) : 
  v[x // n] k = v ⟨k - 1, (nat.sub_lt_right_iff_lt_add $ one_le_of_lt H).2 k.2⟩ :=
have h : ¬(k.val < n.val), from lt_asymm H,
by simp [*, subst_fin_realize]

@[simp] lemma subst_fin_realize_var_eq {S : Type u} {m} (v : fin m → S) (x : S) {n k : fin (m+1)}    (h : n.val = k.val) : v[x // n] k = x :=
by simp [h, subst_fin_realize, lt_irrefl]

lemma subst_fin_realize_congr {S : Type u} {m} {v v' : fin m → S} (hv : ∀k, v k = v' k) (x : S) 
  (n k : fin (m+1)) : v [x // n] k = v' [x // n] k :=
by apply lt_by_cases k.val n.val; intro h; simp*

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

lemma subst_fin_realize_eq {S : Type u} {n} {v₁ : fin n → S} {v₂ : ℕ → S} 
  (hv : ∀k : fin n, v₁ k = v₂ k.val) (x : S) (k : fin (n+1)) : v₁[x // 0] k = v₂[x // 0] k.val :=
begin
  cases k with k hk, cases k, refl, 
  have h : 0 < succ k, from zero_lt_succ k, 
  have h' : (0 : fin (n+1)).val < (fin.mk (succ k) hk).val, from h, 
  rw [subst_realize_gt v₂ x h, subst_fin_realize_gt v₁ x h'], apply hv 
end

/-- The type α → (α → ... (α → β)...) with n α's. We require that α and β live in the same universe, otherwise we have to use ulift. -/
def arity (α β : Type u) : ℕ → Type u
| 0     := β
| (n+1) := α → arity n

def arity_app {α β : Type u} : ∀{l}, arity α β l → dvector α l → β
| _ b []      := b
| _ f (x::xs) := arity_app (f x) xs

def arity_postcompose {α β γ : Type u} (g : β → γ) : ∀{n} (f : arity α β n), arity α γ n
| 0     b := g b
| (n+1) f := λx, arity_postcompose (f x)

def arity_precompose {α β γ : Type u} : ∀{n} (g : arity β γ n) (f : α → β), arity α γ n
| 0     c f := c
| (n+1) g f := λx, arity_precompose (g (f x)) f

inductive arity_respect_setoid {α β : Type u} [R : setoid α] : ∀{n}, arity α β n → Type u
| r_zero (b : β) : @arity_respect_setoid 0 b
| r_succ (n : ℕ) (f : arity α β (n+1)) (h₁ : ∀{{a a'}}, a ≈ a' → f a = f a')
  (h₂ : ∀a, arity_respect_setoid (f a)) : arity_respect_setoid f
open arity_respect_setoid

instance subsingleton_arity_respect_setoid {α β : Type u} [R : setoid α] {n} (f : arity α β n) :
  subsingleton (arity_respect_setoid f) :=
begin
  constructor, intros h h', induction h generalizing h'; cases h'; try {refl}; congr,
  apply funext, intro x, apply h_ih
end

def arity_quotient_lift {α β : Type u} {R : setoid α} : 
  ∀{n}, (Σ(f : arity α β n), arity_respect_setoid f) → arity (quotient R) β n
| _ ⟨_, r_zero b⟩         := b
| _ ⟨_, r_succ n f h₁ h₂⟩ := 
  begin
    apply quotient.lift (λx, arity_quotient_lift ⟨f x, h₂ x⟩),
    intros x x' r, dsimp, 
    apply congr_arg, exact sigma.eq (h₁ r) (subsingleton.elim _ _)
  end

-- def for_all {α : Type u} (P : α → Prop) : Prop := ∀x, P x

-- @[simp] def arity_map2 {α β : Type u} (q : (α → β) → β) (f : β → β → β) : 
--   ∀{n}, arity α β n → arity α β n → β
-- | 0     x y := f x y
-- | (n+1) x y := q (λz, arity_map2 (x z) (y z))

-- @[simp] lemma arity_map2_refl {α : Type} {f : Prop → Prop → Prop} (r : ∀A, f A A) : 
--   ∀{n} (x : arity α Prop n), arity_map2 for_all f x x
-- | 0     x := r x
-- | (n+1) x := λy, arity_map2_refl (x y)

-- def arity_imp {α : Type} {n : ℕ} (f₁ f₂ : arity α Prop n) : Prop := 
-- arity_map2 for_all (λP Q, P → Q) f₁ f₂

-- def arity_iff {α : Type} {n : ℕ} (f₁ f₂ : arity α Prop n) : Prop := 
-- arity_map2 for_all iff f₁ f₂

-- lemma arity_iff_refl {α : Type} {n : ℕ} (f : arity α Prop n) : arity_iff f f := 
-- arity_map2_refl iff.refl f

-- lemma arity_iff_rfl {α : Type} {n : ℕ} {f : arity α Prop n} : arity_iff f f := 
-- arity_iff_refl f


/- 
  Note: we only work in the bottom universe. If we don't, then when we define the realization of
  formulae in a structure S, we want to send preformula n to 
  S → (S → ... → (S → Prop)...)
  with n occurrences of S. If S : Type u, then this type lives in `Type u` for n ≥ 1 and in Type 0 for n = 0, which is super inconvenient/impossible to work with
-/
structure Language : Type 2 := 
(functions : ℕ → Type) (relations : ℕ → Type)

def Language.constants (L : Language) := L.functions 0
section
parameter (L : Language)

/- preterm l is a partially applied term. if applied to n terms, it becomes a term.
* Every element of preterm 0 is well typed. 
* We use this encoding to avoid mutual or nested inductive types, since those are not too convenient to work with in Lean. -/
inductive preterm : ℕ → Type
| var {} : ℕ → preterm 0
| func : ∀ {l : ℕ}, L.functions l → preterm l
| app : ∀ {l : ℕ}, preterm (l + 1) → preterm 0 → preterm l
export preterm

@[reducible] def term := preterm 0

parameter {L}
prefix `&`:max := _root_.fol.preterm.var

def arity_of_preterm : ∀{l}, preterm l → arity term term l
| 0     t := t
| (n+1) t := λs, arity_of_preterm (app t s)

def apps {l} (t : preterm l) (ts : dvector term l) : term :=
arity_app (arity_of_preterm t) ts

/- lift_term_at _ t n m raises variables in t which are at least m by n -/
@[simp] def lift_term_at : ∀ {l}, preterm l → ℕ → ℕ → preterm l
| _ &k          n m := if m ≤ k then &(k+n) else &k
| _ (func f)    n m := func f
| _ (app t₁ t₂) n m := app (lift_term_at t₁ n m) (lift_term_at t₂ n m)

notation t ` ↑' `:90 n ` # `:90 m:90 := _root_.fol.lift_term_at t n m -- input ↑ with \u or \upa

@[reducible] def lift_term {l} (t : preterm l) (n : ℕ) : preterm l := t ↑' n # 0
@[reducible, simp] def lift_term1 {l} (t : preterm l) : preterm l := lift_term t 1

infix ` ↑ `:100 := _root_.fol.lift_term -- input ↑' with \u or \upa
postfix ` ↑1`:100 := _root_.fol.lift_term1 -- input ↑' with \u or \upa

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
lemma lift_term_at₂_small : ∀ {l} (t : preterm l) (n n') {m m'}, m' ≤ m → 
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
  begin dsimp; congr1; apply lift_term_at₂_small; assumption end

lemma lift_term_at₂_medium : ∀ {l} (t : preterm l) {n} (n') {m m'}, m ≤ m' → m' ≤ m+n → 
  (t ↑' n # m) ↑' n' # m' = t ↑' (n+n') # m
| _ &k          n n' m m' H₁ H₂ := 
  begin 
    by_cases h : m ≤ k,
    { have h₁ : m' ≤ k + n, from le_trans H₂ (add_le_add_right h n), simp [*, -add_comm], },
    { have h₁ : ¬m' ≤ k, from λ h', h (le_trans H₁ h'), simp [*, -add_comm, -add_assoc] }
  end
| _ (func f)    n n' m m' H₁ H₂ := by refl
| _ (app t₁ t₂) n n' m m' H₁ H₂ := 
  begin dsimp; congr1; apply lift_term_at₂_medium; assumption end

lemma lift_term2_medium {l} (t : preterm l) {n} (n') {m'} (h : m' ≤ n) :
  (t ↑ n) ↑' n' # m' = t ↑ (n+n') :=
lift_term_at₂_medium t n' m'.zero_le (by simp*)

lemma lift_term2 {l} (t : preterm l) (n n') : (t ↑ n) ↑ n' = t ↑ (n+n') :=
lift_term2_medium t n' n.zero_le

lemma lift_term_at₂_eq {l} (t : preterm l) (n n' m : ℕ) : 
  (t ↑' n # m) ↑' n' # (m+n) = t ↑' (n+n') # m :=
lift_term_at₂_medium t n' (m.le_add_right n) (le_refl _)

lemma lift_term_at₂_large {l} (t : preterm l) {n} (n') {m m'} (H : m + n ≤ m') : 
  (t ↑' n # m) ↑' n' # m' = (t ↑' n' # (m'-n)) ↑' n # m :=
have H₁ : n ≤ m', from le_trans (n.le_add_left m) H,
have H₂ : m ≤ m' - n, from nat.le_sub_right_of_add_le H,
begin rw fol.lift_term_at₂_small t n' n H₂, rw [nat.sub_add_cancel], exact H₁ end

/- subst_term t s n substitutes s for (&n) and reduces the level of all variables above n by 1 -/
def subst_term : ∀ {l}, preterm l → term → ℕ → preterm l
| _ &k          s n := subst_realize var (s ↑ n) n k
| _ (func f)    s n := func f
| _ (app t₁ t₂) s n := app (subst_term t₁ s n) (subst_term t₂ s n)

notation t `[`:max s ` // `:95 n `]`:0 := _root_.fol.subst_term t s n

@[simp] lemma subst_term_var_lt (s : term) {k n : ℕ} (H : k < n) : &k[s // n] = &k :=
by simp [H, subst_term]

@[simp] lemma subst_term_var_gt (s : term) {k n : ℕ} (H : n < k) : &k[s // n] = &(k-1) :=
by simp [H, subst_term]

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
  induction ts generalizing t, refl, apply ts_ih (app t ts_a)
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
    { have h₂ : n₂ < k + (n₁ + 1), from lt_succ_of_le (le_trans h₂ (add_le_add_right h _)), 
      simp [*, add_sub_cancel_right] },
    { have h₂ : k < n₂, from lt_of_lt_of_le (lt_of_not_ge h) h₁, simp* }
  end
| _ (func f)    s n₁ n₂ m h₁ h₂ := rfl
| _ (app t₁ t₂) s n₁ n₂ m h₁ h₂ := by simp*

lemma lift_subst_term_medium {l} (t : preterm l) (s : term) (n₁ n₂) :
  (t ↑ ((n₁ + n₂) + 1))[s // n₁] = t ↑ (n₁ + n₂) :=
lift_at_subst_term_medium t s n₁.zero_le (by rw [zero_add]; exact n₁.le_add_right n₂)

lemma lift_at_subst_term_eq {l} (t : preterm l) (s : term) (n : ℕ) : (t ↑' 1 # n)[s // n] = t :=
begin rw [lift_at_subst_term_medium t s, lift_term_at_zero]; refl end

@[simp] lemma lift_term1_subst_term {l} (t : preterm l) (s : term) : (lift_term1 t)[s // 0] = t :=
lift_at_subst_term_eq t s 0

lemma subst_term2 : ∀{l} (t : preterm l) (s₁ s₂ : term) (n₁ n₂),
  t [s₁ // n₁] [s₂ // n₁ + n₂] = t [s₂ // n₁ + n₂ + 1] [s₁[s₂ // n₂] // n₁]
| _ &k          s₁ s₂ n₁ n₂ :=
  begin -- can we use subst_realize2 here?
    apply lt_by_cases k n₁; intro h,
    { have : k < n₁ + n₂, from lt_of_le_of_lt (k.le_add_right n₂) (by simp*),
      have : k < n₁ + n₂ + 1, from lt.step this,
      simp [*, -add_comm, -add_assoc] },
    { have : k < k + (n₂ + 1), from lt_succ_of_le (le_add_right _ n₂),
      subst h, simp [*, lift_subst_term_large', -add_comm] },
    apply lt_by_cases k (n₁ + n₂ + 1); intro h',
    { have : k - 1 < n₁ + n₂, from (nat.sub_lt_right_iff_lt_add (one_le_of_lt h)).2 h', 
      simp [*, -add_comm, -add_assoc] },
    { subst h', simp [h, lift_subst_term_medium, -add_comm, -add_assoc] },
    { have : n₁ + n₂ < k - 1, from nat.lt_sub_right_of_add_lt h', 
      have : n₁ < k - 1, from lt_of_le_of_lt (n₁.le_add_right n₂) this,
      simp [*, -add_comm, -add_assoc] }
  end
| _ (func f)    s₁ s₂ n₁ n₂ := rfl
| _ (app t₁ t₂) s₁ s₂ n₁ n₂ := by simp*

lemma subst_term2_0 {l} (t : preterm l) (s₁ s₂ : term) (n) :
  t [s₁ // 0] [s₂ // n] = t [s₂ // n + 1] [s₁[s₂ // n] // 0] :=
let h := subst_term2 t s₁ s₂ 0 n in by simp at h; exact h

/- Probably useful facts about substitution which we should add when needed:
(forall M N i j k, ( M [ j ← N] ) ↑' k # (j+i) = (M ↑' k # (S (j+i))) [ j ← (N ↑' k # i ) ])
subst_travers : (forall M N P n, (M [← N]) [n ← P] = (M [n+1 ← P])[← N[n← P]])
erasure_lem1 : (forall a n, a = (a ↑' 1 # (S n)) [n ← #0])
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
inductive preformula : ℕ → Type
| falsum {} : preformula 0
| equal : term → term → preformula 0
| rel : ∀ {l : ℕ}, L.relations l → preformula l
| apprel : ∀ {l : ℕ}, preformula (l + 1) → term → preformula l
| imp : preformula 0 → preformula 0 → preformula 0
| all : preformula 0 → preformula 0
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


def arity_of_preformula : ∀{l}, preformula l → arity term formula l
| 0     f := f
| (n+1) f := λt, arity_of_preformula (apprel f t)

def apps_rel {l} (f : preformula l) (ts : dvector term l) : formula :=
arity_app (arity_of_preformula f) ts

@[simp] def lift_formula_at : ∀ {l}, preformula l → ℕ → ℕ → preformula l
| _ falsum       n m := falsum
| _ (t₁ ≃ t₂)    n m := lift_term_at t₁ n m ≃ lift_term_at t₂ n m
| _ (rel R)      n m := rel R
| _ (apprel f t) n m := apprel (lift_formula_at f n m) (lift_term_at t n m)
| _ (f₁ ⟹ f₂)   n m := lift_formula_at f₁ n m ⟹ lift_formula_at f₂ n m
| _ (∀' f)       n m := ∀' lift_formula_at f n (m+1)

notation f ` ↑' `:90 n ` # `:90 m:90 := _root_.fol.lift_formula_at f n m -- input ↑' with \upa

@[reducible, simp] def lift_formula {l} (f : preformula l) (n : ℕ) : preformula l := f ↑' n # 0
@[reducible, simp] def lift_formula1 {l} (f : preformula l) : preformula l := f ↑' 1 # 0

infix ` ↑ `:100 := _root_.fol.lift_formula -- input ↑' with \upa
postfix ` ↑1`:100 := _root_.fol.lift_formula1 -- input ↑' with \upa

@[simp] lemma lift_formula1_not (f : formula) : lift_formula1 (not f) = not (lift_formula1 f) :=
by refl

lemma lift_formula_at_inj {l} {f f' : preformula l} {n m : ℕ} (H : f ↑' n # m = f' ↑' n # m) : 
  f = f' :=
begin
  induction f generalizing m; cases f'; injection H,
  { simp [lift_term_at_inj h_1, lift_term_at_inj h_2] },
  { simp [f_ih h_1, lift_term_at_inj h_2] },
  { simp [f_ih_a h_1, f_ih_a_1 h_2] },
  { simp [f_ih h_1] }
end

@[simp] lemma lift_formula_at_zero : ∀ {l} (f : preformula l) (m : ℕ), f ↑' 0 # m = f
| _ falsum       m := by refl
| _ (t₁ ≃ t₂)    m := by simp
| _ (rel R)      m := by refl
| _ (apprel f t) m := by simp; apply lift_formula_at_zero
| _ (f₁ ⟹ f₂)   m := by dsimp; congr1; apply lift_formula_at_zero
| _ (∀' f)       m := by simp; apply lift_formula_at_zero

/- the following lemmas simplify iterated lifts, depending on the size of m' -/
lemma lift_formula_at₂_small : ∀ {l} (f : preformula l) (n n') {m m'}, m' ≤ m → 
  (f ↑' n # m) ↑' n' # m' = (f ↑' n' # m') ↑' n # (m + n')
| _ falsum       n n' m m' H := by refl
| _ (t₁ ≃ t₂)    n n' m m' H := by simp [lift_term_at₂_small, H]
| _ (rel R)      n n' m m' H := by refl
| _ (apprel f t) n n' m m' H := 
  by simp [lift_term_at₂_small, H, -add_comm]; apply lift_formula_at₂_small; assumption
| _ (f₁ ⟹ f₂)   n n' m m' H := by dsimp; congr1; apply lift_formula_at₂_small; assumption
| _ (∀' f)       n n' m m' H :=
  by simp [lift_term_at₂_small, H, lift_formula_at₂_small f n n' (add_le_add_right H 1)]

lemma lift_formula_at₂_medium : ∀ {l} (f : preformula l) (n n') {m m'}, m ≤ m' → m' ≤ m+n → 
  (f ↑' n # m) ↑' n' # m' = f ↑' (n+n') # m
| _ falsum       n n' m m' H₁ H₂ := by refl
| _ (t₁ ≃ t₂)    n n' m m' H₁ H₂ := by simp [*, lift_term_at₂_medium]
| _ (rel R)      n n' m m' H₁ H₂ := by refl
| _ (apprel f t) n n' m m' H₁ H₂ := by simp [*, lift_term_at₂_medium, -add_comm]
| _ (f₁ ⟹ f₂)   n n' m m' H₁ H₂ := by simp*
| _ (∀' f)       n n' m m' H₁ H₂ :=
  have m' + 1 ≤ (m + 1) + n, from le_trans (add_le_add_right H₂ 1) (by simp), by simp*

lemma lift_formula_at₂_eq {l} (f : preformula l) (n n' m : ℕ) : 
  (f ↑' n # m) ↑' n' # (m+n) = f ↑' (n+n') # m :=
lift_formula_at₂_medium f n n' (m.le_add_right n) (le_refl _)

lemma lift_formula_at₂_large {l} (f : preformula l) (n n') {m m'} (H : m + n ≤ m') : 
  (f ↑' n # m) ↑' n' # m' = (f ↑' n' # (m'-n)) ↑' n # m :=
have H₁ : n ≤ m', from le_trans (n.le_add_left m) H,
have H₂ : m ≤ m' - n, from nat.le_sub_right_of_add_le H,
begin rw lift_formula_at₂_small f n' n H₂, rw [nat.sub_add_cancel], exact H₁ end

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

@[simp] lemma subst_formula_apps_rel {l} (f : preformula l) (ts : dvector term l) (s : term) (n : ℕ) : (apps_rel f ts)[s // n] = apps_rel (f[s // n]) (ts.map $ λx, x[s // n]) :=
begin
  induction ts generalizing f, refl, apply ts_ih (apprel f ts_a)
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
    have := lift_at_subst_formula_medium f s (add_le_add_right h₁ 1) h, simp at this, simp*
  end

lemma lift_subst_formula_medium {l} (f : preformula l) (s : term) (n₁ n₂) :
  (f ↑ ((n₁ + n₂) + 1))[s // n₁] = f ↑ (n₁ + n₂) :=
lift_at_subst_formula_medium f s n₁.zero_le (by rw [zero_add]; exact n₁.le_add_right n₂)

lemma lift_at_subst_formula_eq {l} (f : preformula l) (s : term) (n : ℕ) : 
  (f ↑' 1 # n)[s // n] = f :=
begin rw [lift_at_subst_formula_medium f s, lift_formula_at_zero]; refl end

@[simp] lemma lift_formula1_subst_formula {l} (f : preformula l) (s : term) : 
  (lift_formula1 f)[s // 0] = f :=
lift_at_subst_formula_eq f s 0

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
let h := subst_formula2 f s₁ s₂ 0 n in by simp at h; exact h

/- Provability
* to decide: should Γ be a list or a set (or finset)?
* We use natural deduction as our deduction system, since that is most convenient to work with.
* All rules are motivated to work well with backwards reasoning.
-/
inductive prf : set formula → formula → Prop
| axm    : ∀{Γ A}, A ∈ Γ → prf Γ A
| impI   : ∀{Γ : set formula} {A B}, prf (insert A Γ) B → prf Γ (A ⟹ B)
| impE   : ∀{Γ} (A) {B}, prf Γ (A ⟹ B) → prf Γ A → prf Γ B
| falseE : ∀{Γ : set formula} {A}, prf (insert ∼A Γ) falsum → prf Γ A
| allI   : ∀{Γ A}, prf (lift_formula1 '' Γ) A → prf Γ (∀' A)
| allE'  : ∀{Γ} A t, prf Γ (∀' A) → prf Γ (A[t // 0])
| refl   : ∀Γ t, prf Γ (t ≃ t)
| subst' : ∀{Γ} s t f, prf Γ (s ≃ t) → prf Γ (f[s // 0]) → prf Γ (f[t // 0])
export prf
infix ` ⊢ `:51 := _root_.fol.prf -- input: \|- or \vdash

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
  { apply axm, exact H₁ H₂_a, },
  { apply impI, apply H₂_ih, apply insert_subset_insert, apply H₁ },
  { apply impE, apply H₂_ih_a, assumption, apply H₂_ih_a_1, assumption },
  { apply falseE, apply H₂_ih, apply insert_subset_insert, apply H₁ },
  { apply allI, apply H₂_ih, apply image_subset _ H₁ },
  { apply allE', apply H₂_ih, assumption },
  { apply refl },
  { apply subst', apply H₂_ih_a, assumption, apply H₂_ih_a_1, assumption },
end

def substitution {Γ} {f : formula} {t n} (H : Γ ⊢ f) : (λx, x[t // n]) '' Γ ⊢ f[t // n] :=
begin
  induction H generalizing n,
  { apply axm, apply mem_image_of_mem _ H_a, },
  { apply impI, have h := @H_ih n, rw [image_insert_eq] at h, exact h },
  { apply impE, apply H_ih_a, apply H_ih_a_1 },
  { apply falseE, have h := @H_ih n, rw [image_insert_eq] at h, exact h },
  { apply allI, rw [←image_comp], have h := @H_ih (n+1), rw [←image_comp] at h, 
    apply cast _ h, congr1, apply image_congr, intros,
    apply lift_subst_formula_large },
  { apply allE _ _ H_ih, symmetry, apply subst_formula2_zero },
  { apply refl },
  { apply subst _ H_ih_a, { have h := @H_ih_a_1 n, rw [subst_formula2_zero] at h, exact h}, 
    rw [subst_formula2_zero] },
end

def weakening1 {Γ} {f₁ f₂ : formula} (H : Γ ⊢ f₂) : insert f₁ Γ ⊢ f₂ :=
weakening (subset_insert f₁ Γ) H

def weakening2 {Γ} {f₁ f₂ f₃ : formula} (H : insert f₁ Γ ⊢ f₂) : insert f₁ (insert f₃ Γ) ⊢ f₂ :=
weakening (insert_subset_insert (subset_insert _ Γ)) H

def deduction {Γ} {A B : formula} (H : Γ ⊢ A ⟹ B) : insert A Γ ⊢ B :=
impE A (weakening1 H) axm1

def exfalso {Γ} {A : formula} (H : Γ ⊢ falsum) : prf Γ A :=
falseE (weakening1 H)

def andI {Γ} {f₁ f₂ : formula} (H₁ : Γ ⊢ f₁) (H₂ : Γ ⊢ f₂) : Γ ⊢ f₁ ⊓ f₂ :=
begin 
  apply impI, apply impE f₂,
  { apply impE f₁, apply axm1, exact weakening1 H₁ },
  { exact weakening1 H₂ }
end

def andE1 {Γ f₁} (f₂ : formula) (H : Γ ⊢ f₁ ⊓ f₂) : Γ ⊢ f₁ :=
begin 
  apply falseE, apply impE _ (weakening1 H), apply impI, apply exfalso,
  apply impE f₁; [apply axm2, apply axm1]
end

def andE2 {Γ} (f₁ : formula) {f₂} (H : Γ ⊢ f₁ ⊓ f₂) : Γ ⊢ f₂ :=
begin apply falseE, apply impE _ (weakening1 H), apply impI, apply axm2 end

def orI1 {Γ} {A B : formula} (H : Γ ⊢ A) : Γ ⊢ A ⊔ B :=
begin apply impI, apply exfalso, refine impE _ _ (weakening1 H), apply axm1 end

def orI2 {Γ} {A B : formula} (H : Γ ⊢ B) : Γ ⊢ A ⊔ B :=
impI $ weakening1 H

def orE {Γ} {A B C : formula} (H₁ : Γ ⊢ A ⊔ B) (H₂ : insert A Γ ⊢ C) (H₃ : insert B Γ ⊢ C) : 
  Γ ⊢ C :=
begin
  apply falseE, apply impE C, { apply axm1 },
  apply impE B, { apply impI, exact weakening2 H₃ },
  apply impE _ (weakening1 H₁),
  apply impI (impE _ axm2 (weakening2 H₂))
end

def biimpI {Γ} {f₁ f₂ : formula} (H₁ : insert f₁ Γ ⊢ f₂) (H₂ : insert f₂ Γ ⊢ f₁) : 
  Γ ⊢ biimp f₁ f₂ :=
by apply andI; apply impI; assumption

def biimpE1 {Γ} {f₁ f₂ : formula} (H : Γ ⊢ f₁ ⇔ f₂) : insert f₁ Γ ⊢ f₂ := deduction (andE1 _ H)
def biimpE2 {Γ} {f₁ f₂ : formula} (H : Γ ⊢ f₁ ⇔ f₂) : insert f₂ Γ ⊢ f₁ := deduction (andE2 _ H)

def exI {Γ f} (t : term) (H : Γ ⊢ f [t // 0]) : Γ ⊢ ∃' f :=
begin
  apply impI, 
  apply impE (f[t // 0]) _ (weakening1 H),
  apply allE' ∼f t axm1,
end

def exE {Γ f₁ f₂} (t : term) (H₁ : Γ ⊢ ∃' f₁) 
  (H₂ : insert f₁ (lift_formula1 '' Γ) ⊢ lift_formula1 f₂) : Γ ⊢ f₂ :=
begin
  apply falseE, apply impE _ (weakening1 H₁), apply allI, apply impI, 
  rw [image_insert_eq], apply impE _ axm2, apply weakening2 H₂
end

def symm {Γ} {s t : term} (H : Γ ⊢ s ≃ t) : Γ ⊢ t ≃ s :=
begin 
  apply subst (&0 ≃ s ↑1) H; rw [subst_formula_equal, lift_term1_subst_term, subst_term_var0],
  apply refl
end

def trans {Γ} {t₁ t₂ t₃ : term} (H : Γ ⊢ t₁ ≃ t₂) (H' : Γ ⊢ t₂ ≃ t₃) : Γ ⊢ t₁ ≃ t₃ :=
begin 
  apply subst (t₁ ↑1 ≃ &0) H'; rw [subst_formula_equal, lift_term1_subst_term, subst_term_var0],
  exact H
end

def congr {Γ} {t₁ t₂ : term} (s : term) (H : Γ ⊢ t₁ ≃ t₂) : Γ ⊢ s[t₁ // 0] ≃ s[t₂ // 0] :=
begin 
  apply subst (s[t₁ // 0] ↑1 ≃ s) H, 
  { rw [subst_formula_equal, lift_term1_subst_term], apply refl },
  { rw [subst_formula_equal, lift_term1_subst_term] }
end

def app_congr {Γ} {t₁ t₂ : term} (s : preterm 1) (H : Γ ⊢ t₁ ≃ t₂) : Γ ⊢ app s t₁ ≃ app s t₂ :=
begin 
  have h := congr (app (s ↑1) &0) H, simp [lift_term1_subst_term] at h, exact h
end

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

def equal_preterms (T : set formula) {l} (t₁ t₂ : preterm l) : Prop :=
∀(ts : dvector term l), T ⊢ apps t₁ ts ≃ apps t₂ ts

def equal_preterms_app {T : set formula} {l} {t t' : preterm (l+1)} {s s' : term} 
  (Ht : equal_preterms T t t') (Hs : T ⊢ s ≃ s') : equal_preterms T (app t s) (app t' s') :=
begin
  intro xs, 
  apply trans (Ht (xs.cons s)),
  have h := congr (apps (t' ↑1) (&0 :: xs.map lift_term1)) Hs, 
  simp [dvector.map_congr (λt, lift_term1_subst_term t s')] at h,
  exact h
end

@[refl] def equal_preterms_refl (T : set formula) {l} (t : preterm l) : equal_preterms T t t :=
λxs, refl T (apps t xs)

def equiv_preformulae (T : set formula) {l} (f₁ f₂ : preformula l) : Prop :=
∀(ts : dvector term l), T ⊢ apps_rel f₁ ts ⇔ apps_rel f₂ ts

def equiv_preformulae_apprel {T : set formula} {l} {f f' : preformula (l+1)} {s s' : term} 
  (Ht : equiv_preformulae T f f') (Hs : T ⊢ s ≃ s') : 
    equiv_preformulae T (apprel f s) (apprel f' s') :=
begin
  intro xs, 
  apply biimp_trans (Ht (xs.cons s)),
  apply subst (apps_rel (f' ↑1) ((s :: xs).map lift_term1) ⇔ 
               apps_rel (f' ↑1) (&0 :: xs.map lift_term1)) Hs; 
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
(carrier : Type) 
(fun_map : ∀{n}, L.functions n → arity carrier carrier n)
(rel_map : ∀{n}, L.relations n → arity carrier Prop n) 
parameter {L}
instance has_coe_Structure : has_coe_to_sort (@_root_.fol.Structure L) :=
⟨Type, Structure.carrier⟩

/- realization of terms -/
@[simp] def realize_term {S : Structure} (v : ℕ → S) : ∀{l}, preterm l → arity S S l
| _ &k          := v k
| _ (func f)    := S.fun_map f
| _ (app t₁ t₂) := realize_term t₁ $ realize_term t₂

lemma realize_term_congr {S : Structure} {v v' : ℕ → S} (h : ∀n, v n = v' n) : 
  ∀{l} (t : preterm l), realize_term v t = realize_term v' t
| _ &k          := h k
| _ (func f)    := by refl
| _ (app t₁ t₂) := by dsimp; rw [realize_term_congr t₁, realize_term_congr t₂]

lemma realize_term_subst {S : Structure} (v : ℕ → S) : ∀{l} (n : ℕ) (t : preterm l) 
  (s : term), realize_term (v[realize_term v (s ↑ n) // n]) t = realize_term v (t[s // n])
| _ n &k          s := 
  by apply lt_by_cases k n; intro h;[simp [h], {subst h; simp}, simp [h]]
| _ n (func f)    s := by refl
| _ n (app t₁ t₂) s := by dsimp; simp*

lemma realize_term_subst_lift {S : Structure} (v : ℕ → S) (x : S) (m : ℕ) : ∀{l} (t : preterm l),
  realize_term (v [x // m]) (t ↑' 1 # m) = realize_term v t
| _ &k          := 
  begin 
    by_cases h : m ≤ k, 
    { have : m < k + 1, from lt_succ_of_le h, simp* },
    { have : k < m, from lt_of_not_ge h, simp* }
  end
| _ (func f)    := by refl
| _ (app t₁ t₂) := by simp*

/- realization of formulas -/
@[simp] def realize_formula {S : Structure} : ∀{l}, (ℕ → S) → preformula l → arity S Prop l
| _ v falsum       := false
| _ v (t₁ ≃ t₂)    := realize_term v t₁ = realize_term v t₂
| _ v (rel R)      := S.rel_map R
| _ v (apprel f t) := realize_formula v f $ realize_term v t
| _ v (f₁ ⟹ f₂)   := realize_formula v f₁ → realize_formula v f₂
| _ v (∀' f)       := ∀(x : S), realize_formula (v [x // 0]) f

lemma realize_formula_congr {S : Structure} : ∀{l} {v v' : ℕ → S} (h : ∀n, v n = v' n) 
  (f : preformula l), realize_formula v f = realize_formula v' f
| _ v v' h falsum       := by refl
| _ v v' h (t₁ ≃ t₂)    := by simp [realize_term_congr h]
| _ v v' h (rel R)      := by refl
| _ v v' h (apprel f t) := by simp [realize_term_congr h]; rw [realize_formula_congr h]
| _ v v' h (f₁ ⟹ f₂)   := by dsimp; rw [realize_formula_congr h, realize_formula_congr h]
| _ v v' h (∀' f)       := 
  by apply forall_eq_congr; intro x; apply realize_formula_congr; intro n; 
     apply subst_realize_congr h

lemma realize_formula_subst {S : Structure} : ∀{l} (v : ℕ → S) (n : ℕ) (f : preformula l) 
  (s : term), realize_formula (v[realize_term v (s ↑ n) // n]) f = realize_formula v (f[s // n]) 
| _ v n falsum       s := by refl
| _ v n (t₁ ≃ t₂)    s := by simp [realize_term_subst]
| _ v n (rel R)      s := by refl
| _ v n (apprel f t) s := by simp [realize_term_subst]; rw realize_formula_subst
| _ v n (f₁ ⟹ f₂)   s := by apply imp_eq_congr; apply realize_formula_subst
| _ v n (∀' f)       s := 
  begin 
    apply forall_eq_congr, intro x, rw [←realize_formula_subst], apply realize_formula_congr, 
    intro k, rw [subst_realize2_0, ←realize_term_subst_lift v x 0, lift_term_def, lift_term2]
  end

lemma realize_formula_subst0 {S : Structure} {l} (v : ℕ → S) (f : preformula l) (s : term) :
  realize_formula (v[realize_term v s // 0]) f = realize_formula v (f[s // 0]) :=
by have h := realize_formula_subst v 0 f s; simp at h; exact h

lemma realize_formula_subst_lift {S : Structure} : ∀{l} (v : ℕ → S) (x : S) (m : ℕ) 
  (f : preformula l), realize_formula (v [x // m]) (f ↑' 1 # m) = realize_formula v f
| _ v x m falsum       := by refl
| _ v x m (t₁ ≃ t₂)    := by simp [realize_term_subst_lift]
| _ v x m (rel R)      := by refl
| _ v x m (apprel f t) := by simp [realize_term_subst_lift]; rw realize_formula_subst_lift
| _ v x m (f₁ ⟹ f₂)   := by apply imp_eq_congr; apply realize_formula_subst_lift
| _ v x m (∀' f)       := 
  begin 
    apply forall_eq_congr, intro x', 
    rw [realize_formula_congr (subst_realize2_0 _ _ _ _), realize_formula_subst_lift]
  end

/- the following definitions of provability and satisfiability are not exactly how you normally define them, since we define it for formulae instead of sentences. If all the formulae happen to be sentences, then these definitions are equivalent to the normal definitions (the realization of closed terms and sentences are independent of the realizer v). 
 -/
def provable (T : set formula) (f : formula) := prf T f
-- infix ` ⊢ `:51 := _root_.fol.provable -- input: \|- or \vdash

def all_provable (T T' : set formula) := ∀{{f}}, f ∈ T' → T ⊢ f
infix ` ⊢ `:51 := _root_.fol.all_provable -- input: |- or \vdash

def satisfied_in (S : Structure) (f : formula) := ∀(v : ℕ → S), realize_formula v f
infix ` ⊨ `:51 := _root_.fol.satisfied_in -- input using \|= or \vDash, but not using \models 

def all_satisfied_in (S : Structure) (T : set formula) := ∀{{f}}, f ∈ T → S ⊨ f
infix ` ⊨ `:51 := _root_.fol.all_satisfied_in -- input using \|= or \vDash, but not using \models 

def satisfied (T : set formula) (f : formula) := 
∀(S : Structure) (v : ℕ → S), (∀f' ∈ T, realize_formula v (f' : formula)) → realize_formula v f

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
  { apply h, simp [H_a] },
  { intro ha, apply H_ih, intros f hf, induction hf, { subst hf, assumption }, apply h f hf },
  { exact H_ih_a v h (H_ih_a_1 v h) },
  { apply classical.by_contradiction, intro ha, 
    apply H_ih v, intros f hf, induction hf, { cases hf, exact ha }, apply h f hf },
  { intro x, apply H_ih, intros f hf, cases (mem_image _ _ _).mp hf with f' hf', induction hf', 
    induction hf'_right, rw [realize_formula_subst_lift v x 0 f'], exact h f' hf'_left },
  { rw [←realize_formula_subst0], apply H_ih v h (realize_term v H_t) },
  { dsimp, refl },
  { have h' := H_ih_a v h, dsimp at h', rw [←realize_formula_subst0, ←h', realize_formula_subst0],
    apply H_ih_a_1 v h },
end

/- sentences and theories -/
inductive term_below (n : ℕ) : ∀{l}, preterm l → Type
| b_var (k) (hk : k < n) : term_below &k
| b_func {} {l} (f : L.functions l) : term_below (func f)
| b_app {l} (t₁ : preterm (l+1)) (t₂) (ht₁ : term_below t₁) (ht₂ : term_below t₂) : 
    term_below (app t₁ t₂)

open term_below 

@[simp] def realize_term_below {S : Structure} {n} (v : fin n → S) : 
  ∀{l} {t : preterm l} (ht : term_below n t), arity S S l
| _ _ (b_var k hk)          := v ⟨k, hk⟩
| _ _ (b_func f)            := S.fun_map f
| _ _ (b_app t₁ t₂ ht₁ ht₂) := realize_term_below ht₁ $ realize_term_below ht₂

@[simp] def term_below_lift {n n' m} : ∀{l} {t : preterm l} (ht : term_below n t), 
  term_below (n + n') (t ↑' n' # m)
| _ _ (b_var k hk)          := sorry
| _ _ (b_func f)            := b_func f
| _ _ (b_app t₁ t₂ ht₁ ht₂) := sorry

@[simp] def term_below_subst {n n'} : ∀{l} {t : preterm l} (ht : term_below (n+n'+1) t) (s : term)
  (hs : term_below n' s), term_below (n+n') (t[s // n])
| _ _ (b_var k hk)          := sorry
| _ _ (b_func f)            := sorry
| _ _ (b_app t₁ t₂ ht₁ ht₂) := sorry

instance subsingleton_term_below (n : ℕ) {l} (t : preterm l) : subsingleton (term_below n t) :=
begin
  constructor, intros h h', induction h generalizing h'; cases h'; try {refl}; congr,
  apply h_ih_ht₁, apply h_ih_ht₂
end

lemma realize_term_below_eq {S : Structure} {n} {v₁ : fin n → S} {v₂ : ℕ → S}
  (hv : ∀k : fin n, v₁ k = v₂ k.val) : ∀{l} {t : preterm l} (ht : term_below n t), 
  realize_term_below v₁ ht = realize_term v₂ t
| _ _ (b_var k hk)          := hv ⟨k, hk⟩
| _ _ (b_func f)            := by refl
| _ _ (b_app t₁ t₂ ht₁ ht₂) := by simp [realize_term_below_eq ht₁, realize_term_below_eq ht₂] 

def closed_preterm (l) := Σ(t : preterm l), term_below 0 t
def closed_term := Σ(t : term), term_below 0 t
def closed_term.eq {t₁ t₂ : closed_term} (h : t₁.fst = t₂.fst) : t₁ = t₂ :=
sigma.eq h (subsingleton.elim _ _)

@[reducible] def closed_term.fst : closed_term → term := sigma.fst

def c_func {l} (f : L.functions l) : closed_preterm l := ⟨func f, b_func f⟩
def c_const (c : L.constants) : closed_term := c_func c
def c_app {l} (t₁ : closed_preterm (l+1)) (t₂ : closed_term) : closed_preterm l := 
⟨app t₁.fst t₂.fst, b_app _ _ t₁.snd t₂.snd⟩

def arity_of_closed_preterm : ∀{l}, closed_preterm l → arity closed_term closed_term l
| 0     t := t
| (n+1) t := λt', arity_of_closed_preterm $ c_app t t'

inductive formula_below : ∀{l}, ℕ → preformula l → Type
| b_falsum {n} : formula_below n falsum
| b_equal {n} (t₁ t₂) (ht₁ : term_below n t₁) (ht₂ : term_below n t₂) : 
    formula_below n (t₁ ≃ t₂)
| b_rel {n l} (R : L.relations l) : formula_below n (rel R)
| b_apprel {n l} (f : preformula (l+1)) (t) (hf : formula_below n f) 
    (ht : term_below n t) : formula_below n (apprel f t)
| b_imp {n} (f₁ f₂ : formula) (hf₁ : formula_below n f₁) (hf₂ : formula_below n f₂) :
    formula_below n (f₁ ⟹ f₂)
| b_all {n} (f : formula) (hf : formula_below (n+1) f) : formula_below n (∀' f)
open formula_below
export formula_below
def b_not (n : ℕ) (f : preformula 0) (hf : formula_below n f)  : formula_below n (fol.not f) := begin
simp[fol.not],
refine b_imp _ _ _ _,
assumption,
exact formula_below.b_falsum
end

def b_and (n : ℕ) (f g : preformula 0) (hf : formula_below n f) (hg : formula_below n g) : formula_below n (fol.and f g) :=
begin
simp[fol.and],
refine b_not _ _ _,
refine formula_below.b_imp _ _ _ _,
assumption,
apply b_not,
assumption
end

def b_biimp (n : ℕ) (f g : preformula 0) (hf : formula_below n f) (hg : formula_below n g) : formula_below n (f ⟺ g) :=
begin
simp[biimp,fol.and, fol.not],
refine formula_below.b_imp _ _ _ _,
have := formula_below.b_falsum, --
refine formula_below.b_imp _ _ _ _,
refine formula_below.b_imp _ _ _ _,
assumption, assumption,
refine formula_below.b_imp _ _ _ _,
refine formula_below.b_imp _ _ _ _,
assumption, assumption, assumption,
exact formula_below.b_falsum,
end

@[simp] def realize_formula_below {S : Structure} : ∀{n} (v : fin n → S)
  {l} {f : preformula l} (hf : formula_below n f), arity S Prop l
| n v _ _ b_falsum                := false
| n v _ _ (b_equal t₁ t₂ ht₁ ht₂) := realize_term_below v ht₁ = realize_term_below v ht₂
| n v _ _ (b_rel R)               := S.rel_map R
| n v _ _ (b_apprel f t hf ht)    := realize_formula_below v hf $ realize_term_below v ht
| n v _ _ (b_imp f₁ f₂ hf₁ hf₂)   := realize_formula_below v hf₁ → realize_formula_below v hf₂
| n v _ _ (b_all f hf)            := ∀(x : S), realize_formula_below (v [x // 0]) hf

instance subsingleton_formula_below (n : ℕ) {l} (f : preformula l) : 
  subsingleton (formula_below n f) :=
begin
  constructor, intros h h', induction h generalizing h'; cases h'; try {refl}; congr,
  apply h_ih, apply h_ih_hf₁, apply h_ih_hf₂, apply h_ih
end

lemma realize_formula_below_eq {S : Structure} : ∀{n} {v₁ : fin n → S} {v₂ : ℕ → S} 
  (hv : ∀k : fin n, v₁ k = v₂ k.val) {l} {f : preformula l} (hf : formula_below n f),
  realize_formula_below v₁ hf = realize_formula v₂ f
| n v₁ v₂ hv _ _ b_falsum                := by refl
| n v₁ v₂ hv _ _ (b_equal t₁ t₂ ht₁ ht₂) := 
  by simp [realize_term_below_eq hv ht₁, realize_term_below_eq hv ht₂]
| n v₁ v₂ hv _ _ (b_rel R)               := by refl
| n v₁ v₂ hv _ _ (b_apprel f t hf ht)    := 
  by simp [realize_term_below_eq hv ht, realize_formula_below_eq hv hf]
| n v₁ v₂ hv _ _ (b_imp f₁ f₂ hf₁ hf₂)   := 
  by apply imp_eq_congr; apply realize_formula_below_eq hv; assumption
| n v₁ v₂ hv _ _ (b_all f hf)            :=
  begin
    apply forall_eq_congr, intro x, apply realize_formula_below_eq _ hf, 
    apply subst_fin_realize_eq hv
  end

def presentence (l : ℕ) := Σ(f : preformula l), formula_below 0 f
def sentence := Σ(f : formula), formula_below 0 f

def sentence.eq {f₁ f₂ : sentence} (h : f₁.fst = f₂.fst) : f₁ = f₂ :=
sigma.eq h (subsingleton.elim _ _)

@[reducible] def sentence.fst : sentence → formula := sigma.fst

def s_falsum : sentence := ⟨falsum, b_falsum⟩ 
notation `⊥` := _root_.fol.s_falsum -- input: \bot
def s_equal (t₁ t₂ : closed_term) : sentence := ⟨t₁.fst ≃ t₂.fst, b_equal _ _ t₁.snd t₂.snd⟩
infix ` ≃ `:88 := _root_.fol.s_equal -- input \~- or \simeq
def s_rel {l} (r : L.relations l) : presentence l := ⟨rel r, b_rel r⟩
def s_apprel {l} (f : presentence (l+1)) (t : closed_term) : presentence l :=
⟨apprel f.fst t.fst, b_apprel _ _ f.snd t.snd⟩
def s_imp (f₁ f₂ : sentence) : sentence := ⟨f₁.fst ⟹ f₂.fst, b_imp _ _ f₁.snd f₂.snd⟩  
infix ` ⟹ `:62 := _root_.fol.s_imp -- input \==>
def s_not (f : sentence) : sentence := f ⟹ ⊥
prefix `∼`:max := _root_.fol.s_not -- input \~, the ASCII character ~ has too low precedence
def s_all (f : formula) (hf : formula_below 1 f) : sentence := ⟨∀' f, b_all f hf⟩
def s_ex (f : formula) (hf : formula_below 1 f) : sentence := 
∼ (s_all (∼ f) (b_imp _ _ hf b_falsum))

def arity_of_presentence : ∀{l}, presentence l → arity closed_term sentence l
| 0     f := f
| (n+1) f := λt, arity_of_presentence $ s_apprel f t

def formula1_subst {f : formula} (hf : formula_below 1 f) (t : closed_term) : sentence :=
⟨f[t.fst // 0], sorry⟩

def realize_sentence (S : Structure) (f : sentence) : Prop := 
realize_formula_below (fin.fin_zero_elim : fin 0 → S) f.snd

lemma realize_sentence_eq {S : Structure} (v : ℕ → S) (f : sentence) : 
  realize_sentence S f = realize_formula v f.fst :=
realize_formula_below_eq (λx, fin.fin_zero_elim x) f.snd

/- theories -/

@[reducible] def Theory := set sentence

@[reducible] def Theory.fst (T : Theory) : set formula := sigma.fst '' T

def sprovable (T : Theory) (f : sentence) := T.fst ⊢ f.fst
infix ` ⊢ `:51 := _root_.fol.sprovable -- input: \|- or \vdash

def saxm {T : Theory} {A : sentence} (H : A ∈ T) : T ⊢ A := 
by apply axm; apply mem_image_of_mem _ H

def sprovable_of_provable {T : Theory} {f : sentence} (h : T.fst ⊢ f.fst) : T ⊢ f := h
def provable_of_sprovable {T : Theory} {f : sentence} (h : T ⊢ f) : T.fst ⊢ f.fst := h

def all_sprovable (T T' : Theory) := ∀(f ∈ T'), T ⊢ f
infix ` ⊢ `:51 := _root_.fol.all_sprovable -- input: \|- or \vdash

infix ` ⊨ `:51 := _root_.fol.realize_sentence -- input using \|= or \vDash, but not using \models 

def all_ssatisfied_in (S : Structure) (T : Theory) := ∀{{f}}, f ∈ T → S ⊨ f
infix ` ⊨ `:51 := _root_.fol.all_ssatisfied_in -- input using \|= or \vDash, but not using \models 

def ssatisfied (T : Theory) (f : sentence) := 
∀{{S : Structure}}, nonempty S → S ⊨ T → S ⊨ f

infix ` ⊨ `:51 := _root_.fol.ssatisfied -- input using \|= or \vDash, but not using \models 

def all_ssatisfied (T T' : Theory) := ∀(f ∈ T'), T ⊨ f
infix ` ⊨ `:51 := _root_.fol.all_ssatisfied -- input using \|= or \vDash, but not using \models 

def satisfied_of_ssatisfied {T : Theory} {f : sentence} (H : T ⊨ f) : T.fst ⊨ f.fst :=
begin
  intros S v hT, rw [←realize_sentence_eq], apply H ⟨ v 0 ⟩,
  intros f' hf', rw [realize_sentence_eq v], apply hT, apply mem_image_of_mem _ hf'
end

def ssatisfied_of_satisfied {T : Theory} {f : sentence} (H : T.fst ⊨ f.fst) : T ⊨ f :=
begin
  intros S hS hT, induction hS with s, rw [realize_sentence_eq (λ_, s)], apply H,
  intros f' hf', rcases hf' with ⟨f', ⟨hf', h⟩⟩, induction h, rw [←realize_sentence_eq],
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

lemma soundness {T : Theory} {A : sentence} (H : T ⊢ A) : T ⊨ A :=
ssatisfied_of_satisfied $ formula_soundness H

def Th (S : Structure) : Theory := { f : sentence | S ⊨ f }

def is_consistent (T : Theory) := ¬(T ⊢ (⊥ : sentence))
def is_complete (T : Theory) := 
is_consistent T ∧ ∀(f : sentence), f ∈ T ∨ ∼ f ∈ T
def has_enough_constants (T : Theory) :=
∃(C : Π(f : formula), formula_below 1 f → L.constants), 
∀(f : formula) (hf : formula_below 1 f), T.fst ⊢ ∃' f ⟹ f[func (C f hf) // 0]

def of_sprovable_of_is_complete {T : Theory} (H : is_complete T) (f : sentence) 
  (Hf : T ⊢ f) : f ∈ T :=
begin 
  cases H.2 f, exact h, exfalso, apply H.1, exact impE _ (saxm h) Hf, 
end

section completeness
parameters {T : Theory} (H₁ : is_complete T) (H₂ : has_enough_constants T)
def completeness_rel (t₁ t₂ : closed_term) : Prop := T ⊢ t₁ ≃ t₂

instance completeness_setoid : setoid closed_term := 
⟨completeness_rel, λt, refl _ _, λt t' H, symm H, λt₁ t₂ t₃ H₁ H₂, trans H₁ H₂⟩

def completeness_Type : Type :=
quotient completeness_setoid

def completeness_fun' {l} (t : closed_preterm l) : arity closed_term completeness_Type l :=
arity_postcompose (@quotient.mk _ completeness_setoid) $ arity_of_closed_preterm $ t

-- def equal_preterms_trans {T : set formula} : ∀{l} {t₁ t₂ t₃ : preterm l} 
--   (h₁₂ : equal_preterms T t₁ t₂) (h₂₃ : equal_preterms T t₂ t₃), equal_preterms T t₁ t₃ 

def completeness_fun_eq {l} (t t' : closed_preterm (l+1)) (x x' : closed_term)
  (Ht : equal_preterms T.fst t.fst t'.fst) (Hx : T ⊢ x ≃ x') : 
  completeness_fun' (c_app t x) = completeness_fun' (c_app t' x') :=
begin
  induction l generalizing x x',
  { apply quotient.sound, apply trans (app_congr t.fst Hx), 
    have := Ht ([x'.fst]), exact this }, 
  { apply funext, intro s, apply l_ih, apply equal_preterms_app Ht Hx, apply refl }
end

def completeness_fun {l} (t : closed_preterm l) : arity completeness_Type completeness_Type l :=
begin
  refine arity_quotient_lift ⟨completeness_fun' t, _⟩,
  induction l,
  { apply r_zero },
  { apply r_succ, 
    { intros x x' r, apply completeness_fun_eq, refl, exact r }, 
    intro x, dsimp [completeness_fun', arity_of_closed_preterm, arity_postcompose], apply l_ih }
end

def completeness_rels' {l} (f : presentence l) : arity closed_term Prop l :=
arity_postcompose (λ(f : sentence), T ⊢ f) $ arity_of_presentence $ f

def completeness_rels_eq {l} (f f' : presentence (l+1)) (x x' : closed_term)
  (Ht : equiv_preformulae T.fst f.fst f'.fst) (Hx : T ⊢ x ≃ x') : 
  completeness_rels' (s_apprel f x) = completeness_rels' (s_apprel f' x') :=
begin
  induction l generalizing x x',
  { apply propext, dsimp [completeness_rels', arity_postcompose, arity_of_presentence], 
    sorry,
    --apply trans (app_congr t.fst Hx), have := Ht ([x'.fst]), exact this 
    }, 
  { apply funext, intro s, apply l_ih, apply equiv_preformulae_apprel Ht Hx, apply refl }
end

def completeness_rels {l} (f : presentence l) : arity completeness_Type Prop l :=
begin
  refine arity_quotient_lift ⟨completeness_rels' f, _⟩, exact T, -- why do we need exact T here?
  induction l,
  { apply r_zero },
  { apply r_succ, 
    { intros x x' r, apply completeness_rels_eq, refl, exact r }, 
    intro x, dsimp [completeness_fun', arity_of_closed_preterm, arity_postcompose], apply l_ih }
end

def completeness_Structure : Structure :=
⟨completeness_Type, 
 λn, completeness_fun ∘ c_func, 
 λn, completeness_rels ∘ s_rel⟩

def completeness_Structure_ssatisfies : completeness_Structure ⊨ T :=
sorry

end completeness

lemma ssatisfies_in_Th (S : Structure) : S ⊨ Th S :=
λf hf, hf

lemma is_complete_Th (S : Structure) (HS : nonempty S) : is_complete (Th S) :=
⟨λH, soundness H HS $ ssatisfies_in_Th S, λ(f : sentence), classical.em (S ⊨ f)⟩

/- maybe define 
presburger_arithmetic := Th (Z,+,0)
true_arithmetic := (ℕ, +, ⬝, 0, 1)
-/

end

structure Lhom (L L' : Language) : Type :=
(on_functions : ∀{n}, L.functions n → L'.functions n) 
(on_relations : ∀{n}, L.relations n → L'.relations n)

local infix ` →ᴸ `:10 := Lhom -- \^L

namespace Lhom

variables {L L' : Language} (ϕ : L →ᴸ L')

protected def on_terms : ∀{l}, preterm L l → preterm L' l
| _ &k          := &k
| _ (func f)    := func $ ϕ.on_functions f
| _ (app t₁ t₂) := app (on_terms t₁) (on_terms t₂)

protected def on_formulae : ∀{l}, preformula L l → preformula L' l
| _ falsum       := falsum
| _ (t₁ ≃ t₂)    := ϕ.on_terms t₁ ≃ ϕ.on_terms t₂
| _ (rel R)      := rel $ ϕ.on_relations R
| _ (apprel f t) := apprel (on_formulae f) $ ϕ.on_terms t
| _ (f₁ ⟹ f₂)   := on_formulae f₁ ⟹ on_formulae f₂
| _ (∀' f)       := ∀' on_formulae f

end Lhom


end fol
