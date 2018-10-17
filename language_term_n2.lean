/- A development of first-order logic in Lean.

* The object theory uses classical logic
* We use de Bruijn variables.
* We use a deep embedding of the logic, i.e. the type of terms and formulas is inductively defined.
* There is no well-formedness predicate; all elements of type "term" are well-formed.
-/

-- this file depends on mathlib
import data.list.basic algebra.ordered_group

universe variable u
namespace nat
lemma add_sub_swap {n k : ℕ} (h : k ≤ n) (m : ℕ) : n + m - k = n - k + m :=
by rw [add_comm, nat.add_sub_assoc h, add_comm]

lemma one_le_of_lt {n k : ℕ} (H : n < k) : 1 ≤ k :=
succ_le_of_lt (lt_of_le_of_lt n.zero_le H)

lemma add_sub_cancel_right (n m k : ℕ) : n + (m + k) - k = n + m :=
by rw [nat.add_sub_assoc, nat.add_sub_cancel]; apply k.le_add_left
end nat

lemma lt_by_cases {α : Type u} [linear_order α] (x y : α) {P : Prop}
  (h₁ : x < y → P) (h₂ : x = y → P) (h₃ : y < x → P) : P :=
or.elim (lt_trichotomy x y) h₁ (λh, or.elim h h₂ h₃)

lemma imp_eq_congr {a b c d : Prop} (h₁ : a = b) (h₂ : c = d) : (a → c) = (b → d) :=
by subst h₁; subst h₂; refl

lemma forall_eq_congr {α : Sort u} {p q : α → Prop} (h : ∀ a, p a = q a) : 
  (∀ a, p a) = ∀ a, q a :=
have h' : p = q, from funext h, by subst h'; refl

namespace list

protected def to_set {α : Type u} (l : list α) : set α := { x | x ∈ l }

end list

namespace tactic
namespace interactive
meta def congr1 : tactic unit := congr_core
end interactive
end tactic

open list nat
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

/- 
  Note: we only work in the bottom universe. If we don't, then when we define the realization of
  formulae in a structure S, we want to send preformula n to 
  S → (S → ... → (S → Prop)...)
  with n occurrences of S. If S : Type u, then this type lives in `Type u` for n ≥ 1 and in Type 0 for n = 0, which is super inconvenient/impossible to work with
-/
structure Language : Type 2 := 
(relations : ℕ → Type) (functions : ℕ → Type)
section
parameter {L : Language}

/- preterm l is a partially applied term. if applied to n terms, it becomes a term.
* Every element of preterm 0 is well typed. 
* We use this encoding to avoid mutual or nested inductive types, since those are not too convenient to work with in Lean. -/
inductive preterm : ℕ → Type
| var : ℕ → preterm 0
| func : ∀ {l : ℕ}, L.functions l → preterm l
| app : ∀ {l : ℕ}, preterm (l + 1) → preterm 0 → preterm l
open preterm
@[reducible] def term := preterm 0

prefix `&`:max := _root_.fol.preterm.var

/- lift_term_at _ t n m raises variables in t which are at least m by n -/
@[simp] def lift_term_at : ∀ {l}, preterm l → ℕ → ℕ → preterm l
| _ &k          n m := if m ≤ k then &(k+n) else &k
| _ (func f)    n m := func f
| _ (app t1 t2) n m := app (lift_term_at t1 n m) (lift_term_at t2 n m)

notation t ` ↑ `:90 n ` # `:90 m:90 := _root_.fol.lift_term_at t n m -- input ↑ with \u or \upa

@[reducible, simp] def lift_term {l} (t : preterm l) (n : ℕ) : preterm l := t ↑ n # 0
@[reducible, simp] def lift_term1 {l} (t : preterm l) : preterm l := t ↑ 1 # 0

infix ` ↑↑ `:100 := _root_.fol.lift_term -- input ↑ with \upa
postfix ` ↑1`:100 := _root_.fol.lift_term1 -- input ↑ with \upa

lemma lift_term_at_inj : ∀ {l} {t t' : preterm l} {n m : ℕ}, t ↑ n # m = t' ↑ n # m → t = t'
| _ &k &k' n m h := 
  by by_cases h₁ : m ≤ k; by_cases h₂ : m ≤ k'; simp [h₁, h₂] at h;
     congr;[assumption, skip, skip, assumption]; exfalso; try {apply h₁}; 
     try {apply h₂}; subst h; apply le_trans (by assumption) (le_add_right _ _)
| _ &k (func f')            n m h := by by_cases h' : m ≤ k; simp [h'] at h; contradiction
| _ &k (app t1' t2')        n m h := by by_cases h' : m ≤ k; simp [h'] at h; contradiction
| _ (func f) &k'            n m h := by by_cases h' : m ≤ k'; simp [h'] at h; contradiction
| _ (func f) (func f')      n m h := h
| _ (func f) (app t1' t2')  n m h := by cases h
| _ (app t1 t2) &k'         n m h := by by_cases h' : m ≤ k'; simp [h'] at h; contradiction
| _ (app t1 t2) (func f')   n m h := by cases h
| _ (app t1 t2) (app t1' t2') n m h := 
  begin injection h, congr; apply lift_term_at_inj; assumption end

@[simp] lemma lift_term_at_zero : ∀ {l} (t : preterm l) (m : ℕ), t ↑ 0 # m = t
| _ &k          m := by simp
| _ (func f)    m := by refl
| _ (app t1 t2) m := by dsimp; congr; apply lift_term_at_zero

/- the following lemmas simplify iterated lifts, depending on the size of m' -/
lemma lift_term_at2_small : ∀ {l} (t : preterm l) (n n') {m m'}, m' ≤ m → 
  (t ↑ n # m) ↑ n' # m' = (t ↑ n' # m') ↑ n # (m + n')
| _ &k          n n' m m' H := 
  begin 
    by_cases h : m ≤ k,
    { have h₁ : m' ≤ k := le_trans H h,
      have h₂ : m' ≤ k + n, from le_trans h₁ (k.le_add_right n),
      simp [*, -add_assoc, -add_comm], simp },
    { have h₁ : ¬m + n' ≤ k + n', from λ h', h (le_of_add_le_add_right h'),
      have h₂ : ¬m + n' ≤ k, from λ h', h₁ (le_trans h' (k.le_add_right n')),
      by_cases h' : m' ≤ k; simp [*, -add_comm, -add_assoc], }
  end
| _ (func f)    n n' m m' H := by refl
| _ (app t1 t2) n n' m m' H := 
  begin dsimp; congr1; apply lift_term_at2_small; assumption end

lemma lift_term_at2_medium : ∀ {l} {t : preterm l} {n n' m m'}, m ≤ m' → m' ≤ m+n → 
  (t ↑ n # m) ↑ n' # m' = t ↑ (n+n') # m
| _ &k          n n' m m' H₁ H₂ := 
  begin 
    by_cases h : m ≤ k,
    { have h₁ : m' ≤ k + n, from le_trans H₂ (add_le_add_right h n),
      simp [*, -add_comm], },
    { simp [h, -add_assoc, -add_comm],
      have h₁ : ¬m' ≤ k, from λ h', h (le_trans H₁ h'),
      simp [*, -add_comm, -add_assoc] }
  end
| _ (func f)    n n' m m' H₁ H₂ := by refl
| _ (app t1 t2) n n' m m' H₁ H₂ := 
  begin dsimp; congr1; apply lift_term_at2_medium; assumption end

lemma lift_term2_medium {l} {t : preterm l} {n n' m'} (h : m' ≤ n) :
  (t ↑↑ n) ↑ n' # m' = t ↑↑ (n+n') :=
lift_term_at2_medium m'.zero_le (by simp*)

lemma lift_term2 {l} {t : preterm l} {n n'} : (t ↑↑ n) ↑↑ n' = t ↑↑ (n+n') :=
lift_term2_medium n.zero_le

lemma lift_term_at2_eq {l} (t : preterm l) (n n' m : ℕ) : 
  (t ↑ n # m) ↑ n' # (m+n) = t ↑ (n+n') # m :=
lift_term_at2_medium (m.le_add_right n) (le_refl _)

lemma lift_term_at2_large {l} (t : preterm l) (n n') {m m'} (H : m + n ≤ m') : 
  (t ↑ n # m) ↑ n' # m' = (t ↑ n' # (m'-n)) ↑ n # m :=
have H₁ : n ≤ m', from le_trans (n.le_add_left m) H,
have H₂ : m ≤ m' - n, from nat.le_sub_right_of_add_le H,
begin rw fol.lift_term_at2_small t n' n H₂, rw [nat.sub_add_cancel], exact H₁ end

/- subst_term t s n substitutes s for (&n) and reduces the level of all variables above n by 1 -/
def subst_term : ∀ {l}, preterm l → term → ℕ → preterm l
| _ &k          s n := subst_realize var (s ↑↑ n) n k
| _ (func f)    s n := func f
| _ (app t1 t2) s n := app (subst_term t1 s n) (subst_term t2 s n)

notation t `[`:max s ` // `:95 n `]`:0 := _root_.fol.subst_term t s n

@[simp] lemma subst_term_var_lt (s : term) {k n : ℕ} (H : k < n) : &k[s // n] = &k :=
by simp [H, subst_term]

@[simp] lemma subst_term_var_gt (s : term) {k n : ℕ} (H : n < k) : &k[s // n] = &(k-1) :=
by simp [H, subst_term]

@[simp] lemma subst_term_var_eq (s : term) (n : ℕ) : &n[s // n] = s ↑ n # 0 :=
by simp [subst_term]

lemma subst_term_var0 (s : term) : &0[s // 0] = s := by simp

@[simp] lemma subst_term_func {l} (f : L.functions l) (s : term) (n : ℕ) : 
  (func f)[s // n] = func f :=
by refl

@[simp] lemma subst_term_app {l} (t₁ : preterm (l+1)) (t₂ s : term) (n : ℕ) : 
  (app t₁ t₂)[s // n] = app (t₁[s // n]) (t₂[s // n]) :=
by refl

/- the following lemmas simplify first lifting and then substituting, depending on the size
  of the substituted variable -/
lemma lift_at_subst_term_large : ∀{l} (t : preterm l) (s : term) {n₁ n₂ m}, m ≤ n₁ →
 (t ↑ n₂ # m)[s // n₁+n₂] = (t [s // n₁]) ↑ n₂ # m
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
| _ (app t1 t2) s n₁ n₂ m h := by simp*

lemma lift_subst_term_large {l} (t : preterm l) (s : term) {n₁ n₂} :
  (t ↑↑ n₂)[s // n₁+n₂] = (t [s // n₁]) ↑↑ n₂ :=
lift_at_subst_term_large t s n₁.zero_le

lemma lift_at_subst_term_medium : ∀{l} (t : preterm l) (s : term) {n₁ n₂ m}, m ≤ n₂ → 
  n₂ ≤ m + n₁ → (t ↑ n₁+1 # m)[s // n₂] = t ↑ n₁ # m
| _ &k          s n₁ n₂ m h₁ h₂ := 
  begin 
    by_cases h : m ≤ k,
    { have h₂ : n₂ < k + (n₁ + 1), from lt_succ_of_le (le_trans h₂ (add_le_add_right h _)), 
      simp [*, add_sub_cancel_right] },
    { have h₂ : k < n₂, from lt_of_lt_of_le (lt_of_not_ge h) h₁, simp* }
  end
| _ (func f)    s n₁ n₂ m h₁ h₂ := rfl
| _ (app t1 t2) s n₁ n₂ m h₁ h₂ := by simp*

lemma lift_subst_term_medium {l} (t : preterm l) (s : term) (n₁ n₂) :
  (t ↑↑ ((n₁ + n₂) + 1))[s // n₁] = t ↑↑ (n₁ + n₂) :=
lift_at_subst_term_medium t s n₁.zero_le (by rw [zero_add]; exact n₁.le_add_right n₂)

lemma lift_at_subst_term_eq {l} (t : preterm l) (s : term) (n : ℕ) : (t ↑ 1 # n)[s // n] = t :=
begin rw [lift_at_subst_term_medium t s, lift_term_at_zero]; refl end

@[simp] lemma lift_term1_subst_term (t s : term) : (lift_term1 t)[s // 0] = t :=
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
      subst h, simp [*, -add_comm], refine eq.trans _ (lift_subst_term_large _ _),
      rw [add_comm] },
    apply lt_by_cases k (n₁ + n₂ + 1); intro h',
    { have : k - 1 < n₁ + n₂, from (nat.sub_lt_right_iff_lt_add (one_le_of_lt h)).2 h', 
      simp [*, -add_comm, -add_assoc] },
    { subst h', simp [h, -add_comm, -add_assoc], symmetry, apply lift_subst_term_medium },
    { have : n₁ + n₂ < k - 1, from nat.lt_sub_right_of_add_lt h', 
      have : n₁ < k - 1, from lt_of_le_of_lt (n₁.le_add_right n₂) this,
      simp [*, -add_comm, -add_assoc] }
  end
| _ (func f)    s₁ s₂ n₁ n₂ := rfl
| _ (app t1 t2) s₁ s₂ n₁ n₂ := by simp*

lemma subst_term2_0 {l} (t : preterm l) (s₁ s₂ : term) (n) :
  t [s₁ // 0] [s₂ // n] = t [s₂ // n + 1] [s₁[s₂ // n] // 0] :=
let h := subst_term2 t s₁ s₂ 0 n in by simp at h; exact h

/- Probably useful facts about substitution which we should add when needed:
(forall M N i j k, ( M [ j ← N] ) ↑ k # (j+i) = (M ↑ k # (S (j+i))) [ j ← (N ↑ k # i ) ])
subst_travers : (forall M N P n, (M [← N]) [n ← P] = (M [n+1 ← P])[← N[n← P]])
erasure_lem1 : (forall a n, a = (a ↑ 1 # (S n)) [n ← #0])
erasure_lem3 : (forall n m t, m>n->#m = (#m ↑ 1 # (S n)) [n ← t]). 
lift_is_lift_sublemma : forall j v, j<v->exists w,#v=w↑1#j. 
lift_is_lift : (forall N A n i j,N ↑ i # n=A ↑ 1 # j -> j<n -> exists M,N=M ↑ 1 # j)
subst_is_lift : (forall N T A n j, N [n ← T]=A↑ 1#j->j<n->exists M,N=M↑ 1#j)
-/

/- preformula l is a partially applied formula. if applied to n terms, it becomes a formula. 
  * We only have implication as binary connective. Since we use classical logic, we can define
    the other connectives from implication and falsum. 
  * Similarly, universal quantification is our only quantifier. 
  * We could make `falsum` and `equal` into elements of rel. However, if we do that, then we cannot make the interpretation of them in a model definitionally what we want.
-/
inductive preformula : ℕ → Type
| falsum : preformula 0
| equal : term → term → preformula 0
| rel : ∀ {l : ℕ}, L.relations l → preformula l
| apprel : ∀ {l : ℕ}, preformula (l + 1) → term → preformula l
| imp : preformula 0 → preformula 0 → preformula 0
| all : preformula 0 → preformula 0
open preformula
@[reducible] def formula := preformula 0

def not (f : formula) : formula := imp f falsum
def and (f₁ f₂ : formula) : formula := not (imp f₁ (not f₂))
def or (f₁ f₂ : formula) : formula := imp (not f₁) f₂
def biimp (f₁ f₂ : formula) : formula := and (imp f₁ f₂) (imp f₂ f₁)
def ex (f : formula) : formula := not (all (not f))

notation `⊥` := _root_.fol.preformula.falsum -- input: \bot
infix ` ≃ `:88 := _root_.fol.preformula.equal -- input \~- or \simeq
infix ` ⟹ `:62 := _root_.fol.preformula.imp -- input \==>
prefix `∼`:max := _root_.fol.not -- input \~
prefix [parsing_only] `~` := _root_.fol.not -- this is the ASCII character. warning: this has a way too low precedence. Use \~ for an operation with a good precedence.
infixr ` ⊔ ` := _root_.fol.or -- input: \sqcup
infixr ` ⊓ ` := _root_.fol.and -- input: \sqcap
prefix `∀∀`:110 := _root_.fol.preformula.all
prefix `∃∃`:110 := _root_.fol.ex

@[simp] def lift_formula_at : ∀ {l}, preformula l → ℕ → ℕ → preformula l
| _ falsum        n m := falsum
| _ (t1 ≃ t2)    n m := equal (lift_term_at t1 n m) (lift_term_at t2 n m)
| _ (rel R)      n m := rel R
| _ (apprel f t) n m := apprel (lift_formula_at f n m) (lift_term_at t n m)
| _ (f1 ⟹ f2)   n m := lift_formula_at f1 n m ⟹ lift_formula_at f2 n m
| _ (∀∀ f)       n m := ∀∀ lift_formula_at f n (m+1)

notation f ` ↑ `:90 n ` # `:90 m:90 := _root_.fol.lift_formula_at f n m -- input ↑ with \upa

@[reducible, simp] def lift_formula {l} (f : preformula l) (n : ℕ) : preformula l := f ↑ n # 0
@[reducible, simp] def lift_formula1 {l} (f : preformula l) : preformula l := f ↑ 1 # 0

infix ` ↑↑ `:100 := _root_.fol.lift_formula -- input ↑ with \upa
postfix ` ↑1`:100 := _root_.fol.lift_formula1 -- input ↑ with \upa

@[simp] lemma lift_formula1_not (f : formula) : lift_formula1 (not f) = not (lift_formula1 f) :=
by refl

lemma lift_formula_at_inj {l} {f f' : preformula l} {n m : ℕ} (H : f ↑ n # m = f' ↑ n # m) : 
  f = f' :=
begin
  induction f generalizing m; cases f'; injection H,
  simp [lift_term_at_inj h_1, lift_term_at_inj h_2],
  simp [f_ih h_1, fol.lift_term_at_inj h_2],
  simp [f_ih_a h_1, f_ih_a_1 h_2],
  simp [f_ih h_1]
end

@[simp] lemma lift_formula_at_zero : ∀ {l} (f : preformula l) (m : ℕ), f ↑ 0 # m = f
| _ falsum       m := by refl
| _ (t1 ≃ t2)    m := by simp
| _ (rel R)      m := by refl
| _ (apprel f t) m := by simp; apply lift_formula_at_zero
| _ (f1 ⟹ f2)   m := by dsimp; congr1; apply lift_formula_at_zero
| _ (∀∀ f)       m := by simp; apply lift_formula_at_zero

/- the following lemmas simplify iterated lifts, depending on the size of m' -/
lemma lift_formula_at2_small : ∀ {l} (f : preformula l) (n n') {m m'}, m' ≤ m → 
  (f ↑ n # m) ↑ n' # m' = (f ↑ n' # m') ↑ n # (m + n')
| _ falsum       n n' m m' H := by refl
| _ (t1 ≃ t2)    n n' m m' H := by simp [lift_term_at2_small, H]
| _ (rel R)      n n' m m' H := by refl
| _ (apprel f t) n n' m m' H := 
  by simp [lift_term_at2_small, H, -add_comm]; apply lift_formula_at2_small; assumption
| _ (f1 ⟹ f2)   n n' m m' H := by dsimp; congr1; apply lift_formula_at2_small; assumption
| _ (∀∀ f)       n n' m m' H :=
  by simp [lift_term_at2_small, H, lift_formula_at2_small f n n' (add_le_add_right H 1)]

lemma lift_formula_at2_medium : ∀ {l} (f : preformula l) (n n') {m m'}, m ≤ m' → m' ≤ m+n → 
  (f ↑ n # m) ↑ n' # m' = f ↑ (n+n') # m
| _ falsum       n n' m m' H₁ H₂ := by refl
| _ (t1 ≃ t2)    n n' m m' H₁ H₂ := by simp [*, lift_term_at2_medium]
| _ (rel R)      n n' m m' H₁ H₂ := by refl
| _ (apprel f t) n n' m m' H₁ H₂ := by simp [*, lift_term_at2_medium, -add_comm]
| _ (f1 ⟹ f2)   n n' m m' H₁ H₂ := by simp*
| _ (∀∀ f)       n n' m m' H₁ H₂ :=
  have m' + 1 ≤ (m + 1) + n, from le_trans (add_le_add_right H₂ 1) (by simp), by simp*

lemma lift_formula_at2_eq {l} (f : preformula l) (n n' m : ℕ) : 
  (f ↑ n # m) ↑ n' # (m+n) = f ↑ (n+n') # m :=
lift_formula_at2_medium f n n' (m.le_add_right n) (le_refl _)

lemma lift_formula_at2_large {l} (f : preformula l) (n n') {m m'} (H : m + n ≤ m') : 
  (f ↑ n # m) ↑ n' # m' = (f ↑ n' # (m'-n)) ↑ n # m :=
have H₁ : n ≤ m', from le_trans (n.le_add_left m) H,
have H₂ : m ≤ m' - n, from nat.le_sub_right_of_add_le H,
begin rw fol.lift_formula_at2_small f n' n H₂, rw [nat.sub_add_cancel], exact H₁ end

@[simp] def subst_formula : ∀ {l}, preformula l → term → ℕ → preformula l
| _ falsum       s n := falsum
| _ (t1 ≃ t2)    s n := subst_term t1 s n ≃ subst_term t2 s n
| _ (rel R)      s n := rel R
| _ (apprel f t) s n := apprel (subst_formula f s n) (subst_term t s n)
| _ (f1 ⟹ f2)   s n := subst_formula f1 s n ⟹ subst_formula f2 s n
| _ (∀∀ f)       s n := ∀∀ subst_formula f s (n+1)

notation f `[`:95 s ` // `:95 n `]`:0 := _root_.fol.subst_formula f s n

lemma subst_formula_equal (t₁ t₂ s : term) (n : ℕ) :
  (t₁ ≃ t₂)[s // n] = t₁[s // n] ≃ (t₂[s // n]) :=
by refl

lemma lift_at_subst_formula_large : ∀{l} (f : preformula l) (s : term) {n₁} (n₂) {m}, m ≤ n₁ →
  (f ↑ n₂ # m)[s // n₁+n₂] = (f [s // n₁]) ↑ n₂ # m
| _ falsum       s n₁ n₂ m h := by refl
| _ (t1 ≃ t2)    s n₁ n₂ m h := by simp [*, lift_at_subst_term_large]
| _ (rel R)      s n₁ n₂ m h := by refl
| _ (apprel f t) s n₁ n₂ m h := by simp [*, lift_at_subst_term_large]
| _ (f1 ⟹ f2)   s n₁ n₂ m h := by simp*
| _ (∀∀ f)       s n₁ n₂ m h := 
  by have := lift_at_subst_formula_large f s n₂ (add_le_add_right h 1); simp at this; simp*

lemma lift_subst_formula_large {l} (f : preformula l) (s : term) {n₁ n₂} :
  (f ↑↑ n₂)[s // n₁+n₂] = (f [s // n₁]) ↑↑ n₂ :=
lift_at_subst_formula_large f s n₂ n₁.zero_le

lemma subst_formula2 : ∀{l} (f : preformula l) (s₁ s₂ : term) (n₁ n₂),
  f [s₁ // n₁] [s₂ // n₁ + n₂] = f [s₂ // n₁ + n₂ + 1] [s₁[s₂ // n₂] // n₁]
| _ falsum       s₁ s₂ n₁ n₂ := by refl
| _ (t1 ≃ t2)    s₁ s₂ n₁ n₂ := by simp [*, subst_term2]
| _ (rel R)      s₁ s₂ n₁ n₂ := by refl
| _ (apprel f t) s₁ s₂ n₁ n₂ := by simp [*, subst_term2]
| _ (f1 ⟹ f2)   s₁ s₂ n₁ n₂ := by simp*
| _ (∀∀ f)       s₁ s₂ n₁ n₂ := 
  by simp*; rw [add_comm n₂ 1, ←add_assoc, subst_formula2 f s₁ s₂ (n₁ + 1) n₂]; simp

lemma subst_formula2_zero {l} (f : preformula l) (s₁ s₂ : term) (n) :
  f [s₁ // 0] [s₂ // n] = f [s₂ // n + 1] [s₁[s₂ // n] // 0] :=
let h := subst_formula2 f s₁ s₂ 0 n in by simp at h; exact h

/- Provability
* to decide: should Γ be a list or a set (or finset)?
* We use natural deduction as our deduction system, since that is most convenient to work with.
* All rules are motivated to work well with backwards reasoning.
-/
inductive prf : list formula → formula → Type
| axm    : ∀{Γ A}, A ∈ Γ → prf Γ A
| impI   : ∀{Γ A B}, prf (A::Γ) B → prf Γ (A ⟹ B)
| impE   : ∀{Γ} (A) {B}, prf Γ (A ⟹ B) → prf Γ A → prf Γ B
| falseE : ∀{Γ A}, prf (∼A::Γ) falsum → prf Γ A
| allI   : ∀{Γ A}, prf (map lift_formula1 Γ) A → prf Γ (∀∀ A)
| allE'  : ∀{Γ} A t, prf Γ (∀∀ A) → prf Γ (A[t // 0])
| refl   : ∀Γ t, prf Γ (t ≃ t)
| subst' : ∀{Γ} s t f, prf Γ (s ≃ t) → prf Γ (f[s // 0]) → prf Γ (f[t // 0])
open prf
infix ` ⊢ `:51 := _root_.fol.prf -- input: \|- or \vdash

def allE {Γ} (A : formula) (t) {B} (H₁ : prf Γ (∀∀ A)) (H₂ : A[t // 0] = B) : prf Γ B :=
by induction H₂; exact allE' A t H₁

def subst {Γ} {s t} (f₁ : formula) {f₂} (H₁ : prf Γ (s ≃ t)) (H₂ : prf Γ (f₁[s // 0])) 
  (H₃ : f₁[t // 0] = f₂) : prf Γ f₂ :=
by induction H₃; exact subst' s t f₁ H₁ H₂

def axm1 {Γ} {A : formula} : A::Γ ⊢ A := by apply axm; left; refl
def axm2 {Γ} {A B : formula} : A::B::Γ ⊢ B := by apply axm; right; left; refl

def weakening {Γ Δ} {f : formula} (H₁ : Γ ⊆ Δ) (H₂ : Γ ⊢ f) : Δ ⊢ f :=
begin
  induction H₂ generalizing Δ,
  { apply axm, exact H₁ H₂_a, },
  { apply impI, apply H₂_ih, simp [cons_subset_cons, H₁] },
  { apply impE, apply H₂_ih_a, assumption, apply H₂_ih_a_1, assumption },
  { apply falseE, apply H₂_ih, simp [cons_subset_cons, H₁] },
  { apply allI, apply H₂_ih, apply map_subset _ H₁ },
  { apply allE', apply H₂_ih, assumption },
  { apply refl },
  { apply subst', apply H₂_ih_a, assumption, apply H₂_ih_a_1, assumption },
end

def substitution {Γ} {f : formula} {t n} (H : Γ ⊢ f) : map (λx, x[t // n]) Γ ⊢ f[t // n] :=
begin
  induction H generalizing n,
  { apply axm, apply mem_map_of_mem _ H_a, },
  { apply impI, apply H_ih },
  { apply impE, apply H_ih_a, apply H_ih_a_1 },
  { apply falseE, apply H_ih },
  { apply allI, rw list.map_map, have h := @H_ih (n+1), rw list.map_map at h, 
    apply cast _ h, congr1; [skip, refl], apply map_congr, intros,
    apply lift_subst_formula_large },
  { apply allE _ _ H_ih, symmetry, apply subst_formula2_zero },
  { apply refl },
  { apply subst _ H_ih_a, { have h := @H_ih_a_1 n, rw [subst_formula2_zero] at h, exact h}, 
    rw [subst_formula2_zero] },
end

def weakening1 {Γ} {f₁ f₂ : formula} (H : Γ ⊢ f₂) : f₁::Γ ⊢ f₂ :=
weakening (Γ.subset_cons f₁) H

def weakening2 {Γ} {f₁ f₂ f₃ : formula} (H : f₁::Γ ⊢ f₂) : f₁::f₃::Γ ⊢ f₂ :=
weakening (cons_subset_cons _ (Γ.subset_cons _)) H

def deduction {Γ} {A B : formula} (H : Γ ⊢ A ⟹ B) : A::Γ ⊢ B :=
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

def orE {Γ} {A B C : formula} (H₁ : Γ ⊢ A ⊔ B) (H₂ : A::Γ ⊢ C) (H₃ : B::Γ ⊢ C) : Γ ⊢ C :=
begin
  apply falseE, apply impE C, { apply axm1 },
  apply impE B, { apply impI, exact weakening2 H₃ },
  apply impE _ (weakening1 H₁),
  apply impI (impE _ axm2 (weakening2 H₂))
end

def biimpI {Γ} {f₁ f₂ : formula} (H₁ : f₁::Γ ⊢ f₂) (H₂ : f₂::Γ ⊢ f₁) : Γ ⊢ biimp f₁ f₂ :=
by apply andI; apply impI; assumption

def biimpE1 {Γ} {f₁ f₂ : formula} (H : Γ ⊢ biimp f₁ f₂) : f₁::Γ ⊢ f₂ :=
deduction (andE1 _ H)

def biimpE2 {Γ} {f₁ f₂ : formula} (H : Γ ⊢ biimp f₁ f₂) : f₂::Γ ⊢ f₁ :=
deduction (andE2 _ H)

def exI {Γ f} (t : term) (H : Γ ⊢ f [t // 0]) : Γ ⊢ ∃∃ f :=
begin
  apply impI, 
  apply impE (f[t // 0]) _ (weakening1 H),
  apply allE' ∼f t axm1,
end

def exE {Γ f₁ f₂} (t : term) (H₁ : Γ ⊢ ∃∃ f₁) (H₂ : f₁::map lift_formula1 Γ ⊢ lift_formula1 f₂) :
  Γ ⊢ f₂ :=
begin
  apply falseE, apply impE _ (weakening1 H₁), apply allI, apply impI, 
  apply impE _ axm2, apply weakening2 H₂
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

def congr {Γ} {t₁ t₂ s : term} (H : Γ ⊢ t₁ ≃ t₂) : Γ ⊢ s[t₁ // 0] ≃ s[t₂ // 0] :=
begin 
  apply subst (s[t₁ // 0] ↑1 ≃ s) H, 
  { rw [subst_formula_equal, lift_term1_subst_term], apply refl },
  { rw [subst_formula_equal, lift_term1_subst_term] }
end

/- sentences -/
def term_variables_below : Π{l}, preterm l → ℕ → Prop
| _ &k          n := if k < n then true else false
| _ (func f)    n := true
| _ (app t1 t2) n := term_variables_below t1 n ∧ term_variables_below t2 n

def formula_variables_below : Π{l}, preformula l → ℕ → Prop
| _ falsum       n := true
| _ (t1 ≃ t2)    n := term_variables_below t1 n ∧ term_variables_below t2 n 
| _ (rel R)      n := true
| _ (apprel f t) n := formula_variables_below f n ∧ term_variables_below t n
| _ (f1 ⟹ f2)   n := formula_variables_below f1 n ∧ formula_variables_below f2 n
| _ (∀∀ f)       n := formula_variables_below f (n+1)

def is_sentence {l} (t : preformula l) := formula_variables_below t 0
def sentence := { t : formula // is_sentence t }

/- model theory -/

/-- The type α → (α → ... (α → β)...) with n α's. We require that α and β live in the same universe, otherwise we have to use ulift. -/
def arity (α β : Type u) : ℕ → Type u
| 0     := β
| (n+1) := α → arity n

-- def for_all {α : Type u} (P : α → Prop) : Prop := ∀x, P x

-- @[simp] def arity_map2 {α β : Type u} (q : (α → β) → β) (f : β → β → β) : 
--   ∀{n}, arity α β n → arity α β n → β
-- | 0     x y := f x y
-- | (n+1) x y := q (λz, arity_map2 (x z) (y z))

-- @[simp] lemma arity_map2_refl {α : Type} {f : Prop → Prop → Prop} (r : ΠA, f A A) : 
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

structure Structure :=
(carrier : Type) 
(fun_map : ∀{n}, L.functions n → arity carrier carrier n)
(rel_map : ∀{n}, L.relations n → arity carrier Prop n) 

instance : has_coe_to_sort (@_root_.fol.Structure L) :=
⟨Type, Structure.carrier⟩

/- realization of terms -/
@[simp] def realize_term {S : Structure} (v : ℕ → S) : Π{l}, preterm l → arity S S l
| _ &k          := v k
| _ (func f)    := S.fun_map f
| _ (app t1 t2) := realize_term t1 $ realize_term t2

lemma realize_term_congr {S : Structure} {v v' : ℕ → S} (h : ∀n, v n = v' n) : 
  Π{l} (t : preterm l), realize_term v t = realize_term v' t
| _ &k          := h k
| _ (func f)    := by refl
| _ (app t1 t2) := by dsimp; rw [realize_term_congr t1, realize_term_congr t2]

lemma realize_term_subst {S : Structure} (v : ℕ → S) : Π{l} (n : ℕ) (t : preterm l) 
  (s : term), realize_term (v[realize_term v (s ↑↑ n) // n]) t = realize_term v (t[s // n])
| _ n &k          s := 
  by apply lt_by_cases k n; intro h;[simp [h], {subst h; simp}, simp [h]]
| _ n (func f)    s := by refl
| _ n (app t1 t2) s := by dsimp; simp*

lemma realize_term_subst_lift {S : Structure} (v : ℕ → S) (x : S) (m : ℕ) : Π{l} (t : preterm l),
  realize_term (v [x // m]) (t ↑ 1 # m) = realize_term v t
| _ &k          := 
  begin 
    by_cases h : m ≤ k, 
    { have : m < k + 1, from lt_succ_of_le h, simp* },
    { have : k < m, from lt_of_not_ge h, simp* }
  end
| _ (func f)    := by refl
| _ (app t1 t2) := by simp*

/- realization of formulas -/
@[simp] def realize_formula {S : Structure} : Π{l}, (ℕ → S) → preformula l → arity S Prop l
| _ v falsum       := false
| _ v (t1 ≃ t2)    := realize_term v t1 = realize_term v t2
| _ v (rel R)      := S.rel_map R
| _ v (apprel f t) := realize_formula v f $ realize_term v t
| _ v (f1 ⟹ f2)   := realize_formula v f1 → realize_formula v f2
| _ v (∀∀ f)       := ∀(x : S), realize_formula (v [x // 0]) f

lemma realize_formula_congr {S : Structure} : Π{l} {v v' : ℕ → S} (h : ∀n, v n = v' n) 
  (f : preformula l), realize_formula v f = realize_formula v' f
| _ v v' h falsum       := by refl
| _ v v' h (t1 ≃ t2)    := by simp [realize_term_congr h]
| _ v v' h (rel R)      := by refl
| _ v v' h (apprel f t) := by simp [realize_term_congr h]; rw [realize_formula_congr h]
| _ v v' h (f1 ⟹ f2)   := by dsimp; rw [realize_formula_congr h, realize_formula_congr h]
| _ v v' h (∀∀ f)       := 
  by apply forall_eq_congr; intro x; apply realize_formula_congr; intro n; 
     apply subst_realize_congr h

lemma realize_formula_subst {S : Structure} : Π{l} (v : ℕ → S) (n : ℕ) (f : preformula l) 
  (s : term), realize_formula (v[realize_term v (s ↑↑ n) // n]) f = realize_formula v (f[s // n]) 
| _ v n falsum       s := by refl
| _ v n (t1 ≃ t2)    s := by simp [realize_term_subst]
| _ v n (rel R)      s := by refl
| _ v n (apprel f t) s := by simp [realize_term_subst]; rw realize_formula_subst
| _ v n (f1 ⟹ f2)   s := by dsimp; apply imp_eq_congr; apply realize_formula_subst
| _ v n (∀∀ f)       s := 
  begin 
    apply forall_eq_congr, intro x, rw [←realize_formula_subst], apply realize_formula_congr, 
    intro k, rw [subst_realize2_0, ←realize_term_subst_lift v x 0, lift_term2_medium n.zero_le]
  end

lemma realize_formula_subst0 {S : Structure} {l} (v : ℕ → S) (f : preformula l) (s : term) :
  realize_formula (v[realize_term v s // 0]) f = realize_formula v (f[s // 0]) :=
let h := realize_formula_subst v 0 f s in by simp at h; exact h

lemma realize_formula_subst_lift {S : Structure} : Π{l} (v : ℕ → S) (x : S) (m : ℕ) 
  (f : preformula l), realize_formula (v [x // m]) (f ↑ 1 # m) = realize_formula v f
| _ v x m falsum       := by refl
| _ v x m (t1 ≃ t2)    := by simp [realize_term_subst_lift]
| _ v x m (rel R)      := by refl
| _ v x m (apprel f t) := by simp [realize_term_subst_lift]; rw realize_formula_subst_lift
| _ v x m (f1 ⟹ f2)   := by dsimp; apply imp_eq_congr; apply realize_formula_subst_lift
| _ v x m (∀∀ f)       := 
  begin 
    apply forall_eq_congr, intro x', 
    rw [realize_formula_congr (subst_realize2_0 _ _ _ _), realize_formula_subst_lift]
  end

/- the following definitions of provability and satisfiability are not exactly how you normally define them, since we define it for formulae instead of sentences. If all the formulae happen to be sentences, then these definitions are equivalent to the normal definitions (the realization of closed terms and sentences are independent of the realizer v). 
We could do it for sentences, but then things get a little uglier. 
 -/
def provable (T : set formula) (f : formula) :=
∃(Γ : list formula), Γ.to_set ⊆ T ∧ nonempty (Γ ⊢ f)
infix ` ⊢ `:51 := _root_.fol.provable -- input: \|- or \vdash

def all_provable (T : set formula) (S : set formula) := ∀(f ∈ S), T ⊢ f
infix ` ⊢ `:51 := _root_.fol.all_provable -- input: \|- or \vdash

def satisfied_in (S : Structure) (f : formula) := ∀(v : ℕ → S), realize_formula v f

infix ` ⊨ `:51 := _root_.fol.satisfied_in -- input using \|= or \vDash, but not using \models 

def satisfied (T : set formula) (f : formula) :=
∀(S : Structure) (v : ℕ → S), (∀f' ∈ T, realize_formula v (f' : formula)) → realize_formula v f

infix ` ⊨ `:51 := _root_.fol.satisfied -- input using \|= or \vDash, but not using \models 

def sweakening {T T' : set formula} (H : T ⊆ T') {f : formula} (HT : T ⊨ f) : T' ⊨ f :=
λS v h, HT S v $ λf Hf, h f $ H Hf

def all_satisfied (T : set formula) (S : set formula) :=
∀(f ∈ S), T ⊨ f

/- soundness for a list of formulae -/
lemma soundness' {Γ : list formula} {A : formula} (H : Γ ⊢ A) : Γ.to_set ⊨ A :=
begin
  intro S, induction H; intros v h,
  { apply h, simp [H_a, list.to_set] },
  { intro ha, apply H_ih, intros f hf, induction hf, { subst hf, assumption }, apply h f hf },
  { exact H_ih_a v h (H_ih_a_1 v h) },
  { apply classical.by_contradiction, intro ha, 
    apply H_ih v, intros f hf, induction hf, { cases hf, exact ha }, apply h f hf },
  { intro x, apply H_ih, intros f hf, cases exists_of_mem_map hf with f' hf', induction hf', 
    induction hf'_right, rw [realize_formula_subst_lift v x 0 f'], exact h f' hf'_left },
  { rw [←realize_formula_subst0], apply H_ih v h (realize_term v H_t) },
  { dsimp, refl },
  { have h' := H_ih_a v h, dsimp at h', rw [←realize_formula_subst0, ←h', realize_formula_subst0],
    apply H_ih_a_1 v h },
end

/- soundness for a set of formulae -/
lemma soundness {T : set formula} {A : formula} (H : T ⊢ A) : T ⊨ A :=
by rcases H with ⟨Γ, ⟨H1, ⟨H2⟩⟩⟩; exact sweakening H1 (soundness' H2)


end
end fol
open fol fol.preterm
variable {L : Language}
