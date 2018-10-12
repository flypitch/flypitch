/- A development of first-order logic in Lean.

* The object theory uses classical logic
* We use de Bruijn variables.
* We use a deep embedding of the logic, i.e. the type of terms and formulas is inductively defined.
* There is no well-formedness predicate; all elements of type "term" are well-formed.
-/

-- depend on mathlib
--import data.list.basic

namespace tactic
namespace interactive
meta def congr1 : tactic unit := congr_core
end interactive
end tactic

open list
namespace fol
structure Language := 
(relations : ℕ → Type) (functions : ℕ → Type)
section
parameter {L : Language}

/- preterm n is a partially applied term. if applied to n terms, it becomes a term.
* Every element of preterm 0 is well typed. 
* We use this encoding to avoid mutual or nested inductive types, since those are not too convenient to work with in Lean. -/
inductive preterm : ℕ → Type 
| var : ℕ → preterm 0
| func : ∀ {n : nat}, L.functions n → preterm n
| apply : ∀ {n : nat}, preterm (n + 1) → preterm 0 → preterm n
open preterm
@[reducible] def term := preterm 0

prefix `&`:max := _root_.fol.preterm.var

/- lift_term_at _ t n m raises variables in t which are at least m by n -/
@[simp] def lift_term_at : ∀ {l}, preterm l → ℕ → ℕ → preterm l
| _ &k            n m := if m ≤ k then &(k+n) else &k
| _ (func f)      n m := func f
| _ (apply t1 t2) n m := apply (lift_term_at t1 n m) (lift_term_at t2 n m)

notation t ` ↑ `:100 n ` # `:100 m:100 := _root_.fol.lift_term_at t n m -- input ↑ with \upa

def lift_term (t : term) (n : ℕ) : term := t ↑ n # 0
def lift_term1 (t : term) : term := t ↑ 1 # 0

infix ` ↑↑ `:100 := _root_.fol.lift_term -- input ↑ with \upa
postfix ` ↑1`:100 := _root_.fol.lift_term1 -- input ↑ with \upa

lemma lift_term_at_inj : ∀ {l} {t t' : preterm l} {n m : ℕ}, t ↑ n # m = t' ↑ n # m → t = t'
| _ &k &k' n m h := 
  by by_cases h₁ : m ≤ k; by_cases h₂ : m ≤ k'; simp [h₁, h₂] at h; 
     congr;[exact add_right_cancel h, skip, skip, assumption]; exfalso; try {apply h₁}; 
     try {apply h₂}; subst h; apply le_trans (by assumption) (nat.le_add_right _ _)
| _ &k (func f')              n m h := by by_cases h' : m ≤ k; simp [h'] at h; contradiction
| _ &k (apply t1' t2')        n m h := by by_cases h' : m ≤ k; simp [h'] at h; contradiction
| _ (func f) &k'              n m h := by by_cases h' : m ≤ k'; simp [h'] at h; contradiction
| _ (func f) (func f')        n m h := h
| _ (func f) (apply t1' t2')  n m h := by cases h
| _ (apply t1 t2) &k'         n m h := by by_cases h' : m ≤ k'; simp [h'] at h; contradiction
| _ (apply t1 t2) (func f')   n m h := by cases h
| _ (apply t1 t2) (apply t1' t2') n m h := 
  begin injection h, congr; apply lift_term_at_inj; assumption end

@[simp] lemma lift_term_at_zero : ∀ {l} (t : preterm l) (m : ℕ), t ↑ 0 # m = t
| _ &k            m := by simp
| _ (func f)      m := by refl
| _ (apply t1 t2) m := by dsimp; congr; apply lift_term_at_zero

/- the following lemmas simplify iterated lifts, depending on the size of m' -/
lemma lift_term_at2_small : ∀ {l} (t : preterm l) (n n') {m m'}, m' ≤ m → 
  (t ↑ n # m) ↑ n' # m' = (t ↑ n' # m') ↑ n # (m + n')
| _ &k            n n' m m' H := 
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
| _ &k            n n' m m' H₁ H₂ := 
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
  (t ↑ n # m) ↑ n' # m' = (t ↑ n' # (m'-n)) ↑ n # m :=
have H₁ : n ≤ m', from le_trans (n.le_add_left m) H,
have H₂ : m ≤ m' - n, by rw [←nat.add_sub_cancel m n]; apply nat.sub_le_sub_right; exact H,
begin rw fol.lift_term_at2_small t n' n H₂, rw [nat.sub_add_cancel], exact H₁ end

/- substitute_term t s n substitutes s for (&n) and reduces the level of all variables above n by 1 -/
@[simp] def substitute_term : ∀ {l}, preterm l → term → ℕ → preterm l
| _ &k            s n := if k < n then &k else if n < k then &(k-1) else s
| _ (func f)      s n := func f
| _ (apply t1 t2) s n := apply (substitute_term t1 s n) (substitute_term t2 s n)

notation t `[`:95 s ` // `:95 n `]`:0 := _root_.fol.substitute_term t s n

@[simp] def substitute_term_var_eq (t : term) (n : ℕ) : &n[t // n] = t :=
by simp [lt_irrefl]

lemma substitute_term_lift_term' : ∀{l} (t : preterm l) (s : term) (n : ℕ), 
  (lift_term_at t 1 n)[s // n] = t :=
sorry

@[simp] lemma substitute_term_lift_term (t s : term) : (lift_term1 t)[s // 0] = t :=
substitute_term_lift_term' t s 0

/- preformula n is a partially applied formula. if applied to n terms, it becomes a formula. 
  * We only have implication as binary connective. Since we use classical logic, we can define
    the other connectives from implication and false. 
  * Similarly, universal quantification is our only quantifier. 
  * We could make `false` and `equal` into elements of rel. However, if we do that, then we cannot make the interpretation of them in a model definitionally what we want.

-/
inductive preformula : ℕ → Type 
| false : preformula 0
| equal : term → term → preformula 0
| rel : ∀ {n : nat}, L.relations n → preformula n
| apprel : ∀ {n : nat}, preformula (n + 1) → term → preformula n
| imp : preformula 0 → preformula 0 → preformula 0
| all : preformula 0 → preformula 0
open preformula
@[reducible] def formula := preformula 0

def not (f : formula) : formula := imp f false
def and (f₁ f₂ : formula) : formula := not (imp f₁ (not f₂))
def or (f₁ f₂ : formula) : formula := imp (not f₁) f₂
def iff (f₁ f₂ : formula) : formula := and (imp f₁ f₂) (imp f₂ f₁)
def ex (f : formula) : formula := not (all (not f))

notation `⊥` := _root_.fol.preformula.false -- input: \bot
infix ` ≃ `:90 := _root_.fol.preformula.equal -- input \~- or \simeq
infix ` ⟹ `:70 := _root_.fol.preformula.imp -- input \==>
prefix `~` := _root_.fol.not
infixr ` ⊔ `:80 := _root_.fol.or -- input: \sqcup
infixr ` ⊓ `:85 := _root_.fol.and -- input: \sqcap


@[simp] def lift_formula_at : ∀ {l}, preformula l → ℕ → ℕ → preformula l
| _ false        n m := false
| _ (t1 ≃ t2)    n m := equal (lift_term_at t1 n m) (lift_term_at t2 n m)
| _ (rel R)      n m := rel R
| _ (apprel f t) n m := apprel (lift_formula_at f n m) (lift_term_at t n m)
| _ (imp f1 f2)  n m := imp (lift_formula_at f1 n m) (lift_formula_at f2 n m)
| _ (all f)      n m := all (lift_formula_at f n (m+1))

notation f ` ↑ `:100 n ` # `:100 m:100 := _root_.fol.lift_formula_at f n m -- input ↑ with \upa

def lift_formula (f : formula) (n : ℕ) : formula := f ↑ n # 0
def lift_formula1 (f : formula) : formula := f ↑ 1 # 0

lemma lift_formula_at_inj {l} {f f' : preformula l} {n m : ℕ} (H : f ↑ n # m = f' ↑ n # m) : f = f' :=
begin
  induction f generalizing m; cases f'; injection H,
  simp [lift_term_at_inj h_1, lift_term_at_inj h_2],
  simp [f_ih h_1, fol.lift_term_at_inj h_2],
  simp [f_ih_a h_1, f_ih_a_1 h_2],
  simp [f_ih h_1]
end

@[simp] lemma lift_formula_at_zero : ∀ {l} (f : preformula l) (m : ℕ), f ↑ 0 # m = f
| _ false        m := by refl
| _ (t1 ≃ t2)    m := by simp
| _ (rel R)      m := by refl
| _ (apprel f t) m := by simp; apply lift_formula_at_zero
| _ (imp f1 f2)  m := by dsimp; congr1; apply lift_formula_at_zero
| _ (all f)      m := by simp; apply lift_formula_at_zero

/- the following lemmas simplify iterated lifts, depending on the size of m' -/
lemma lift_formula_at2_small : ∀ {l} (f : preformula l) (n n') {m m'}, m' ≤ m → 
  (f ↑ n # m) ↑ n' # m' = (f ↑ n' # m') ↑ n # (m + n')
| _ false        n n' m m' H := by refl
| _ (t1 ≃ t2)    n n' m m' H := by simp [lift_term_at2_small, H]
| _ (rel R)      n n' m m' H := by refl
| _ (apprel f t) n n' m m' H := 
  by simp [lift_term_at2_small, H, -add_comm]; apply lift_formula_at2_small; assumption
| _ (imp f1 f2)  n n' m m' H := by dsimp; congr1; apply lift_formula_at2_small; assumption
| _ (all f)      n n' m m' H :=
  by simp [lift_term_at2_small, H, lift_formula_at2_small f n n' (add_le_add_right H 1)]

lemma lift_formula_at2_medium : ∀ {l} (f : preformula l) (n n') {m m'}, m ≤ m' → m' ≤ m+n → 
  (f ↑ n # m) ↑ n' # m' = f ↑ (n+n') # m
| _ false        n n' m m' H₁ H₂ := by refl
| _ (t1 ≃ t2)    n n' m m' H₁ H₂ := by simp [lift_term_at2_medium, H₁, H₂]
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
  (f ↑ n # m) ↑ n' # m' = (f ↑ n' # (m'-n)) ↑ n # m :=
have H₁ : n ≤ m', from le_trans (n.le_add_left m) H,
have H₂ : m ≤ m' - n, by rw [←nat.add_sub_cancel m n]; apply nat.sub_le_sub_right; exact H,
begin rw fol.lift_formula_at2_small f n' n H₂, rw [nat.sub_add_cancel], exact H₁ end

@[simp] def substitute_formula : ∀ {l}, preformula l → term → ℕ → preformula l
| _ false        s n := false
| _ (t1 ≃ t2)    s n := equal (substitute_term t1 s n) (substitute_term t2 s n)
| _ (rel R)      s n := rel R
| _ (apprel f t) s n := apprel (substitute_formula f s n) (substitute_term t s n)
| _ (imp f1 f2)  s n := imp (substitute_formula f1 s n) (substitute_formula f2 s n)
| _ (all f)      s n := all (substitute_formula f s (n+1))

notation f `[`:95 s ` // `:95 n `]`:0 := _root_.fol.substitute_formula f s n

@[simp] def substitute_formula_equal (t₁ t₂ s : term) (n : ℕ) :
  (t₁ ≃ t₂)[s // n] = t₁[s // n] ≃ (t₂[s // n]) :=
by refl

-- ⟹⇔≃
/- Provability relation
* to decide: should Γ be a list or a set (or finset)?
* We use natural deduction as our deduction system, since that is most convenient to work with.
* All rules are motivated to work well with backwards reasoning.
-/
inductive prf : list formula → formula → Type
| axm    : ∀{Γ A}, A ∈ Γ → prf Γ A
| impI   : ∀{Γ A B}, prf (A::Γ) B → prf Γ (A ⟹ B)
| impE   : ∀{Γ} (A) {B}, prf Γ (A ⟹ B) → prf Γ A → prf Γ B
| falseE : ∀{Γ A}, prf (not A::Γ) false → prf Γ A
| allI   : ∀{Γ A}, prf (map lift_formula1 Γ) A → prf Γ (all A)
| allE'  : ∀{Γ} A t, prf Γ (all A) → prf Γ (A[t // 0])
| refl   : ∀Γ t, prf Γ (t ≃ t)
| subst' : ∀{Γ} s t f, prf Γ (s ≃ t) → prf Γ (f[s // 0]) → prf Γ (f[t // 0])
open prf
infix ` ⊢ `:51 := _root_.fol.prf -- input: \|- or \vdash

def weakening {Γ Δ} {f : formula} (H₁ : Γ ⊆ Δ) (H₂ : Γ ⊢ f) : Δ ⊢ f :=
begin
  induction H₂ generalizing Δ,
  { apply axm, exact H₁ H₂_a, },
  { apply impI, apply H₂_ih, simp [cons_subset_cons, H₁] },
  { apply impE, apply H₂_ih_a, assumption, apply H₂_ih_a_1, assumption },
  { apply falseE, apply H₂_ih, simp [cons_subset_cons, H₁] },
  { apply allI, apply H₂_ih, sorry /-simp [cons_subset_cons, H₁]-/ },
  { apply allE', apply H₂_ih, assumption },
  { apply refl },
  { apply subst', apply H₂_ih_a, assumption, apply H₂_ih_a_1, assumption },
end

def weakening_cons {Γ} {f₁ f₂ : formula} (H : Γ ⊢ f₂) : f₁::Γ ⊢ f₂ :=
weakening (Γ.subset_cons f₁) H

def weakening_cons2 {Γ} {f₁ f₂ f₃ : formula} (H : f₁::Γ ⊢ f₂) : f₁::f₃::Γ ⊢ f₂ :=
weakening (cons_subset_cons _ (Γ.subset_cons _)) H

def allE {Γ} (A : formula) (t) {B} (H₁ : prf Γ (all A)) (H₂ : A[t // 0] = B) : prf Γ B :=
by induction H₂; exact allE' A t H₁

def subst {Γ} {s t} (f₁ : formula) {f₂} (H₁ : prf Γ (s ≃ t)) (H₂ : prf Γ (f₁[s // 0])) 
  (H₃ : f₁[t // 0] = f₂) : prf Γ f₂ :=
by induction H₃; exact subst' s t f₁ H₁ H₂

def axm1 {Γ} {A : formula} : A::Γ ⊢ A := by apply axm; left; refl
def axm2 {Γ} {A B : formula} : A::B::Γ ⊢ B := by apply axm; right; left; refl

def deduction {Γ} {A B : formula} (H : Γ ⊢ A ⟹ B) : A::Γ ⊢ B :=
impE A (weakening_cons H) axm1

def exfalso {Γ} {A : formula} (H : prf Γ false) : prf Γ A :=
falseE (weakening_cons H)

def andI {Γ} {f₁ f₂ : formula} (H₁ : Γ ⊢ f₁) (H₂ : Γ ⊢ f₂) : Γ ⊢ f₁ ⊓ f₂ :=
begin 
  apply impI, apply impE f₂,
  { apply impE f₁, apply axm1, exact weakening_cons H₁ },
  { exact weakening_cons H₂ }
end

def andE1 {Γ f₁} (f₂ : formula) (H : Γ ⊢ f₁ ⊓ f₂) : Γ ⊢ f₁ :=
begin 
  apply falseE, apply impE _ (weakening_cons H), apply impI, apply exfalso,
  apply impE f₁; [apply axm2, apply axm1]
end

def andE2 {Γ} (f₁ : formula) {f₂} (H : Γ ⊢ f₁ ⊓ f₂) : Γ ⊢ f₂ :=
begin 
  apply falseE, apply impE _ (weakening_cons H), apply impI, apply axm2
end

def orI1 {Γ} {A B : formula} (H : Γ ⊢ A) : Γ ⊢ A ⊔ B :=
begin
  apply impI, apply exfalso, refine impE _ _ (weakening_cons H), apply axm1
end

def orI2 {Γ} {A B : formula} (H : Γ ⊢ B) : Γ ⊢ A ⊔ B :=
impI $ weakening_cons H

def orE {Γ} {A B C : formula} (H₁ : Γ ⊢ A ⊔ B) (H₂ : A::Γ ⊢ C) (H₃ : B::Γ ⊢ C) : Γ ⊢ C :=
begin
  apply falseE, apply impE C, { apply axm1 },
  apply impE B, { apply impI, exact weakening_cons2 H₃ },
  apply impE _ (weakening_cons H₁),
  apply impI (impE _ axm2 (weakening_cons2 H₂))
end

def iffI {Γ} {f₁ f₂ : formula} (H₁ : f₁::Γ ⊢ f₂) (H₂ : f₂::Γ ⊢ f₁) : Γ ⊢ iff f₁ f₂ :=
by apply andI; apply impI; assumption

def iffE1 {Γ} {f₁ f₂ : formula} (H : Γ ⊢ iff f₁ f₂) : f₁::Γ ⊢ f₂ :=
deduction (andE1 _ H)

def iffE2 {Γ} {f₁ f₂ : formula} (H : Γ ⊢ iff f₁ f₂) : f₂::Γ ⊢ f₁ :=
deduction (andE2 _ H)

-- def ex (f : formula) : formula := not (all (not f))

def symm {Γ} {s t : term} (H : Γ ⊢ s ≃ t) : Γ ⊢ t ≃ s :=
begin 
  apply subst (&0 ≃ s ↑1) H; 
    rw [substitute_formula_equal, substitute_term_lift_term, substitute_term_var_eq],
  apply refl
end

def trans {Γ} {t₁ t₂ t₃ : term} (H : Γ ⊢ t₁ ≃ t₂) (H' : Γ ⊢ t₂ ≃ t₃) : Γ ⊢ t₁ ≃ t₃ :=
begin 
  apply subst (t₁ ↑1 ≃ &0) H';
    rw [substitute_formula_equal, substitute_term_lift_term, substitute_term_var_eq],
  exact H
end

def congr {Γ} {t₁ t₂ s : term} (H : Γ ⊢ t₁ ≃ t₂) : Γ ⊢ s[t₁ // 0] ≃ s[t₂ // 0] :=
begin 
  apply subst (s[t₁ // 0] ↑1 ≃ s) H, 
  { rw [substitute_formula_equal, substitute_term_lift_term], apply refl },
  { rw [substitute_formula_equal, substitute_term_lift_term] }
end

end
end fol
open fol fol.preterm
variable {L : Language}
