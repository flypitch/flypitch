/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
import set_theory.zfc order.complete_boolean_algebra
       .to_mathlib order.zorn .pSet_ordinal

local infix ` ⟹ `:65 := lattice.imp

local infix ` ⇔ `:50 := lattice.biimp

-- uncomment in case of emergency
-- @[tidy] meta def big_bertha : tactic unit := `[finish]

namespace lattice

section natded
variables {𝔹 : Type*} [complete_boolean_algebra 𝔹]

lemma supr_imp_eq {ι : Type*} {s : ι → 𝔹} {b : 𝔹} :
  (⨆(i:ι), s i) ⟹ b = (⨅(i:ι), s i ⟹ b) :=
by {unfold imp, rw[neg_supr, infi_sup_eq]}

lemma imp_infi_eq {ι : Type*} {s : ι → 𝔹} {b : 𝔹} :
  (b ⟹ (⨅i, s i)) = (⨅i, b ⟹ s i) :=
by {unfold imp, rw[sup_infi_eq]}

lemma bv_Or_elim  {ι : Type*} {s : ι → 𝔹} {c : 𝔹} :
(∀ i : ι, (s i ≤ c)) → ((⨆(i:ι), s i) ≤ c) :=
λ H, by apply supr_le; from H

lemma bv_And_intro {ι : Type*} {s : ι → 𝔹} {b c : 𝔹} :
(∀ i : ι, (c ≤ s i)) → (c ≤ ⨅(i:ι), s i) :=
λ H, by {apply le_infi, from H} -- this is superceded by tactic.interactive.bv_intro

lemma bv_or_elim {b₁ b₂ c : 𝔹} {h : b₁ ≤ c} {h' : b₂ ≤ c} : b₁ ⊔ b₂ ≤ c :=
  by apply sup_le; assumption

lemma bv_or_elim_left {b₁ b₂ c d : 𝔹} {h₁ : b₁ ⊓ d ≤ c} {h₂ : b₂ ⊓ d ≤ c} : (b₁ ⊔ b₂) ⊓ d ≤ c :=
  by {rw[deduction], apply bv_or_elim; rw[<-deduction]; from ‹_›}

lemma bv_or_elim_right {b₁ b₂ c d : 𝔹} {h₁ : d ⊓ b₁ ≤ c} {h₂ : d ⊓ b₂ ≤ c} : d ⊓ (b₁ ⊔ b₂) ≤ c :=
  by {rw[inf_comm] at ⊢ h₁ h₂; apply bv_or_elim_left; assumption}

lemma bv_exfalso {a b : 𝔹} (h : a ≤ ⊥) : a ≤ b :=
le_trans h bot_le

lemma bv_cases_left {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} {h : ∀ i : ι, (s i ⊓ c ≤ b)} :
  ((⨆(i:ι), s i) ⊓ c) ≤ b :=
by {rw[deduction], apply supr_le, intro i, rw[<-deduction], revert i, from ‹_›}

lemma bv_cases_right {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} {h : ∀ i : ι, (c ⊓ s i ≤ b)} :
  (c ⊓ (⨆(i:ι), s i)) ≤ b :=
by {rw[inf_comm], apply bv_cases_left, simpa only [inf_comm]}

lemma bv_specialize {ι : Type*} {s : ι → 𝔹} (i : ι) {b : 𝔹} {h : s i ≤ b} :
(⨅(i:ι), s i) ≤ b := infi_le_of_le i h

--TODO(jesse) write the version of this for an arbitrary list of instantiations
lemma bv_specialize_twice {ι : Type*} {s : ι → 𝔹} (i j : ι) {b : 𝔹} {h : s i ⊓ s j ≤ b} :
(⨅(i:ι), s i) ≤ b :=
begin
  apply le_trans', apply infi_le, from i, apply le_trans', apply inf_le_left_of_le,
  apply infi_le, from j, apply le_trans _ h, apply inf_le_inf, apply inf_le_right, refl
end

lemma bv_specialize_left {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} (i : ι)
  {h : s i ⊓ c ≤ b} : (⨅(i:ι), s i) ⊓ c ≤ b :=
by {rw[deduction], apply bv_specialize i, rwa[<-deduction]}

lemma bv_specialize_left_twice {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} (i j : ι)
  {h : s i ⊓ s j ⊓ c ≤ b} : (⨅(i:ι), s i) ⊓ c ≤ b :=
begin
  rw[deduction], apply bv_specialize_twice i j, rwa[<-deduction]
end

lemma bv_specialize_right {ι : Type*} {s :ι → 𝔹} {c b : 𝔹} (i : ι)
  {h : c ⊓ s i ≤ b} : c ⊓ (⨅(i:ι), s i) ≤ b :=
by {rw[inf_comm], apply bv_specialize_left i, rwa[inf_comm]}

lemma bv_specialize_right_twice {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} (i j : ι)
  {h : c ⊓ (s i ⊓ s j) ≤ b} : c ⊓ (⨅(i:ι), s i) ≤ b :=
begin
  rw[inf_comm], apply bv_specialize_left_twice i j, rwa[<-inf_comm]
end

lemma bv_imp_elim {a b : 𝔹} : (a ⟹ b) ⊓ a ≤ b :=
by simp[imp, inf_sup_right]

lemma bv_imp_elim' {a b : 𝔹} : (a ⟹ b) ⊓ a ≤ a ⊓ b :=
by {simp[imp, inf_sup_right]}

lemma bv_cancel_antecedent {a b c : 𝔹} (h : b ≤ c) : a ⟹ b ≤ a ⟹ c :=
by {rw[<-deduction], apply le_trans, apply bv_imp_elim, from ‹_›}

-- example {a b c : 𝔹} (h : b ≤ c) : a ⟹ b ≤ a ⟹ c :=
-- by {tidy_context, bv_imp_intro, apply (poset_yoneda_inv _ h), from a_1 ‹_›}

lemma bv_and_intro {a b₁ b₂ : 𝔹} (h₁ : a ≤ b₁) (h₂ : a ≤ b₂) : a ≤ b₁ ⊓ b₂ := le_inf h₁ h₂

lemma bv_or_left {a b₁ b₂ : 𝔹} (h₁ : a ≤ b₁) : a ≤ b₁ ⊔ b₂ := le_sup_left_of_le h₁

lemma bv_or_right {a b₁ b₂ : 𝔹} (h₂ : a ≤ b₂) : a ≤ b₁ ⊔ b₂ := le_sup_right_of_le h₂

lemma bv_and.left {a b : 𝔹} {Γ} (H : Γ ≤ a ⊓ b) : Γ ≤ a :=
le_trans H inf_le_left

lemma bv_and.right {a b : 𝔹} {Γ} (H : Γ ≤ a ⊓ b) : Γ ≤ b :=
le_trans H inf_le_right

lemma from_empty_context {a b : 𝔹} (h : ⊤ ≤ b) : a ≤ b :=
  by refine le_trans _ h; apply le_top

lemma bv_imp_intro {a b c : 𝔹} {h : a ⊓ b ≤ c} :
  a ≤ b ⟹ c := by rwa[deduction] at h

lemma bv_have {a b c : 𝔹} (h : a ≤ b) {h' : a ⊓ b ≤ c} : a ≤ c :=
by {rw[(inf_self.symm : a = _)], apply le_trans, apply inf_le_inf, refl, exact h, exact h'}

lemma bv_have_true {a b c : 𝔹} (h₁ : ⊤ ≤ b) (h₂ : a ⊓ b ≤ c) : a ≤ c :=
by {rw[top_le_iff] at h₁, rw[h₁] at h₂, from le_trans (by rw[inf_top_eq]) h₂}

lemma bv_use {ι} (i : ι) {s : ι → 𝔹} {b : 𝔹}  {h : b ≤ s i} : b ≤ ⨆(j:ι), s j :=
  le_supr_of_le i h

lemma bv_context_apply {β : Type*} [complete_boolean_algebra β] {Γ a₁ a₂ : β}
  (h₁ : Γ ≤ a₁ ⟹ a₂) (h₂ : Γ ≤ a₁) : Γ ≤ a₂ := h₁ ‹_›

lemma bv_by_contra {Γ b : 𝔹} {H : Γ ≤ (-b) ⟹ ⊥} : Γ ≤ b := by simpa using H

lemma bv_Or_imp {Γ : 𝔹} {ι} {ϕ₁ ϕ₂ : ι → 𝔹} (H_sub : Γ ≤ ⨅ x, ϕ₁ x ⟹ ϕ₂ x) (H : Γ ≤ ⨆x, ϕ₁ x)  : Γ ≤ ⨆x, ϕ₂ x :=
by {bv_cases_at H x, apply bv_use x, from H_sub x ‹_›}

end natded
end lattice

open lattice

universe u

namespace pSet

/-- If two pre-sets `x` and `y` are not equivalent, then either there exists a member of x
which is not equivalent to any member of y, or there exists a member of y which is not
equivalent to any member of x -/
lemma not_equiv {x y : pSet} (h_neq : ¬ pSet.equiv x y) :
  (∃ a : x.type, ∀ a' : y.type, ¬ pSet.equiv (x.func a) (y.func a')) ∨
  (∃ a' : y.type, ∀ a : x.type, ¬ pSet.equiv (x.func a) (y.func a')) :=
begin
  cases x, cases y, unfold equiv, safe,
  suffices : equiv (mk x_α x_A) (mk y_α y_A), by contradiction,
  constructor; assumption
end

end pSet


/- A 𝔹-valued model of ZFC -/

-- τ is a B-name if and only if τ is a set of pairs of the form ⟨σ, b⟩, where σ is
-- a B-name and b ∈ B.
inductive bSet (𝔹 : Type u) [complete_boolean_algebra 𝔹] : Type (u+1)
| mk (α : Type u) (A : α → bSet) (B : α → 𝔹) : bSet

namespace bSet
variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

noncomputable instance decidable_eq_𝔹 : decidable_eq 𝔹 := λ _ _, classical.prop_decidable _

run_cmd mk_simp_attr `cleanup

/-- The underlying type of a bSet -/
@[simp, cleanup]def type : bSet 𝔹 → Type u
| ⟨α, _, _⟩ := α

@[simp, cleanup]lemma type_infi {α : Type*} {A : α → bSet 𝔹} {B C : α → 𝔹} : (⨅(a : type (mk α A B)), C a) = ⨅(a : α), C a := rfl

@[simp, cleanup]lemma type_supr {α : Type*} {A : α → bSet 𝔹} {B C : α → 𝔹} : (⨆(a : type (mk α A B)), C a) = ⨆(a : α), C a := rfl

/-- The indexing function of a bSet -/
@[simp, cleanup]def func : ∀ x : bSet 𝔹, x.type → bSet 𝔹
| ⟨_, A, _⟩ := A

/-- The boolean truth-value function of a bSet -/
@[simp, cleanup]def bval : ∀ x : bSet 𝔹, x.type → 𝔹
| ⟨_, _, B⟩ := B

@[simp, cleanup]def mk_type_func_bval : ∀ x : bSet 𝔹, mk x.type x.func x.bval = x :=
  λ x, by cases x; refl

def empty : bSet 𝔹 :=
  ⟨ulift empty, empty.elim ∘ ulift.down, empty.elim ∘ ulift.down⟩

instance nonempty_bSet : nonempty $ @bSet 𝔹 _ :=
  ⟨empty⟩

instance has_empty_bSet : has_emptyc (bSet 𝔹) := ⟨empty⟩

@[simp]lemma forall_over_empty (ϕ : (type (∅ : bSet 𝔹)) → 𝔹) : (⨅a, ϕ a) = ⊤ :=
  by {apply top_unique, bv_intro a, repeat{cases a}}

@[simp]lemma exists_over_empty (ϕ : (type (∅ : bSet 𝔹)) → 𝔹) : (⨆a, ϕ a) = ⊥ :=
 by {apply bot_unique, apply bv_Or_elim, intro i, repeat{cases i}}

/-- Two Boolean-valued pre-sets are extensionally equivalent if every
element of the first family is extensionally equivalent to
  some element of the second family and vice-versa. -/
@[reducible]def bv_eq : ∀ (x y : bSet 𝔹), 𝔹
| ⟨α, A, B⟩ ⟨α', A', B'⟩ :=
             (⨅a : α, B a ⟹ ⨆a', B' a' ⊓ bv_eq (A a) (A' a')) ⊓
               (⨅a' : α', B' a' ⟹ ⨆a, B a ⊓ bv_eq (A a) (A' a'))

infix ` =ᴮ `:80 := bv_eq

def bv_eq' (Γ : 𝔹) : bSet 𝔹 → bSet 𝔹 → Prop := λ x y, Γ ≤ x=ᴮ y

theorem bv_eq_refl_empty : (@bv_eq 𝔹 _) (empty) (empty) = ⊤ :=
  by unfold empty bv_eq;
  {simp only [lattice.inf_eq_top_iff, lattice.infi_eq_top], fsplit; intros i; cases i; cases i}

open lattice

@[simp]theorem bv_eq_refl : ∀ x, @bv_eq 𝔹 _ x x = ⊤ :=
begin
  intro x, induction x, simp[bv_eq, -imp_top_iff_le], split; intros;
  {apply top_unique, simp only [lattice.top_le_iff, lattice.imp_top_iff_le],
    apply le_supr_of_le i, have := x_ih i, simp[this]}
end

@[simp]theorem bv_refl {Γ : 𝔹} {x} : Γ ≤ x =ᴮ x := le_trans le_top (by simp)

@[simp]lemma bv_eq_top_of_eq {x y : bSet 𝔹} (h_eq : x = y) : x =ᴮ y = ⊤ :=
by simp*

/- empty' is the singleton bSet {⟨∅, ⊥⟩}, i.e. a set whose only member is ∅ which has
   a zero probability of actually being an element. It should be equivalent to ∅. -/
@[reducible]def empty' : bSet 𝔹 := mk punit (λ _, ∅) (λ _, ⊥)

example : empty =ᴮ empty = (⊤ : 𝔹) := by simp

example : ⊤ ≤ empty =ᴮ (empty' : bSet 𝔹) :=
by simp[empty, empty']; exact dec_trivial

/-- `x ∈ y` as Boolean-valued pre-sets if `x` is extensionally equivalent to a member
  of the family `y`. -/
@[reducible, simp]def mem : bSet 𝔹 → bSet 𝔹 → 𝔹
| a (mk α' A' B') := ⨆a', B' a' ⊓ a =ᴮ A' a'

@[reducible]def empty'' : bSet 𝔹 :=
  mk (ulift bool) (λ x, ∅) (λ x, by {repeat{cases x}, exact ⊥, exact ⊤})

infix ` ∈ᴮ `:80 := mem

lemma mem_unfold {u v : bSet 𝔹} : u ∈ᴮ v = ⨆(i : v.type), v.bval i ⊓ u =ᴮ v.func i :=
by cases v; simp

/-- ∅ appears in empty'' with probability 0 and 1, with the higher probability winning the
    vote of membership. This demonstrates why the inequality in the following theorem is
    necessary. -/
example : ∅ ∈ᴮ empty'' = (⊤ : 𝔹) :=
  by {apply top_unique, apply le_supr_of_le ⊤, swap, exact ⟨⟨(tt)⟩⟩, simp}

theorem mem.mk {α : Type*} (A : α → bSet 𝔹) (B : α → 𝔹) (a : α) : B a ≤ A a ∈ᴮ mk α A B :=
  le_supr_of_le a $ by simp

theorem mem.mk' (x : bSet 𝔹) (a : x.type) : x.bval a ≤ x.func a ∈ᴮ x :=
by {cases x, apply le_supr_of_le a, simp}

-- the Γ-generalized version of mem.mk uses two primes because mem.mk' already existed
theorem mem.mk'' {x : bSet 𝔹} {a : x.type} {Γ} : Γ ≤ x.bval a → Γ ≤ x.func a ∈ᴮ x :=
poset_yoneda_inv Γ (mem.mk' x a)

@[reducible]protected def subset : bSet 𝔹 → bSet 𝔹 → 𝔹
| (mk α A B) b := ⨅a:α, B a ⟹ (A a ∈ᴮ b)

infix ` ⊆ᴮ `:80 := bSet.subset

lemma subset_unfold {x u : bSet 𝔹} : x ⊆ᴮ u = (⨅(j : x.type), x.bval j ⟹ x.func j ∈ᴮ u) :=
by induction x; dsimp[bSet.subset]; congr

@[simp]protected def insert : bSet 𝔹 → 𝔹 → bSet 𝔹 → bSet 𝔹
| u b ⟨α, A, B⟩ := ⟨option α, λo, option.rec u A o, λo, option.rec b B o⟩

protected def insert' : bSet 𝔹 → 𝔹 → bSet 𝔹 → bSet 𝔹
| u b ⟨α, A, B⟩ := ⟨unit ⊕ α, λ o, sum.rec (λ_, u) A o, λ o, sum.rec (λ_, b) B o⟩

@[reducible]protected def insert1 : bSet 𝔹 → bSet 𝔹 → bSet 𝔹
| u v := bSet.insert u ⊤ v

lemma insert1_unfold {u v : bSet 𝔹} :
  bSet.insert1 u v = ⟨option v.type, λo, option.rec u v.func o, λ o, option.rec ⊤ v.bval o⟩ :=
by {induction v, simp[bSet.insert1]}

-- @[simp]lemma insert1_type {u v : bSet 𝔹} : (bSet.insert1 u v).type = option v.type := by simp[insert1_unfold]

instance insert_bSet : has_insert (bSet 𝔹) (bSet 𝔹) :=
  ⟨λ u v, bSet.insert1 u v⟩

@[simp]lemma insert_unfold {y z : bSet 𝔹} : insert y z = bSet.insert y ⊤ z :=
  by refl

@[simp]theorem mem_insert {x y z : bSet 𝔹} {b : 𝔹} :
  x ∈ᴮ bSet.insert y b z = (b ⊓ x =ᴮ y) ⊔ x ∈ᴮ z :=
  by induction y; induction z; simp

@[simp]theorem mem_insert1 {x y z : bSet 𝔹} : x ∈ᴮ insert y z = x =ᴮ y ⊔ x ∈ᴮ z :=
  by simp

example : {∅} =ᴮ empty'' = (⊤ : 𝔹) :=
begin
  simp[empty'', singleton, insert, has_insert.insert], simp[has_emptyc.emptyc, empty,bSet.insert1],
  refine ⟨_, by intro i; repeat{cases i}⟩, apply top_unique,
 have : ⊤ = (ulift.rec (bool.rec ⊥ ⊤) : ulift bool → 𝔹) (ulift.up tt),
   by refl,
 rw[this], apply le_supr
end

theorem bv_eq_symm {x y : bSet 𝔹} : x =ᴮ y = y =ᴮ x :=
begin
  induction x with α A B generalizing y, induction y with α' A' B',
  suffices : ∀ a : α, ∀ a' : α', A' a' =ᴮ A a = A a =ᴮ A' a',
    by {simp[bv_eq, this, inf_comm]}, from λ _ _, by simp[x_ih ‹α›]
end

theorem bv_eq_unfold (x y : bSet 𝔹) :
  x =ᴮ y = (⨅(a : x.type), x.bval a ⟹ (x.func a ∈ᴮ y))
          ⊓ (⨅(a' : y.type), (y.bval a' ⟹ (y.func a' ∈ᴮ x))) :=
 by induction x; induction y; simp[mem,bv_eq,bv_eq_symm]

theorem bSet_axiom_of_extensionality (x y : bSet 𝔹) :
(⨅(z : bSet 𝔹), (z ∈ᴮ x ⟹ z ∈ᴮ y) ⊓ (z ∈ᴮ y ⟹ z ∈ᴮ x)) ≤ x =ᴮ y :=
begin
  rw[bv_eq_unfold],
  apply le_inf; apply le_infi; intro i,
  {fapply infi_le_of_le (x.func i), apply inf_le_left_of_le,
   induction x, unfold mem, simp only with cleanup,
   by apply imp_le_of_left_le; apply le_supr_of_le i;
   exact le_inf (by refl) (by rw[bv_eq_refl]; apply le_top)},
  {fapply infi_le_of_le (y.func i), apply inf_le_right_of_le,
   induction y, unfold mem, simp only with cleanup,
   by apply imp_le_of_left_le; apply le_supr_of_le i;
   exact le_inf (by refl) (by rw[bv_eq_refl]; apply le_top)},
end

lemma eq_of_subset_subset (x y : bSet 𝔹) : x ⊆ᴮ y ⊓ y ⊆ᴮ x ≤ x =ᴮ y :=
begin
  simp[subset_unfold, bv_eq_unfold], tidy;
  [apply inf_le_left_of_le, apply inf_le_right_of_le]; apply bv_specialize i; refl
end

lemma subset_subset_of_eq (x y : bSet 𝔹) : x =ᴮ y ≤ x ⊆ᴮ y ⊓ y ⊆ᴮ x :=
begin
  simp[subset_unfold, bv_eq_unfold], tidy;
  [apply inf_le_left_of_le, apply inf_le_right_of_le]; apply bv_specialize i; refl
end

theorem eq_iff_subset_subset {x y : bSet 𝔹} : x =ᴮ y = x ⊆ᴮ y ⊓ y ⊆ᴮ x :=
by apply le_antisymm; [apply subset_subset_of_eq, apply eq_of_subset_subset]

lemma subset_of_eq {x y : bSet 𝔹} {Γ} (H : Γ ≤ x =ᴮ y) : Γ ≤ x ⊆ᴮ y ∧ Γ ≤ y ⊆ᴮ x :=
by {rw[eq_iff_subset_subset] at H, bv_split, exact ⟨‹_›,‹_›⟩}

@[simp]lemma subset_self {x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ x ⊆ᴮ x :=
by {apply le_trans, apply le_top, rw[show ⊤ = x =ᴮ x, by simp[bv_eq_refl]], rw[eq_iff_subset_subset], apply inf_le_left}

theorem subset_ext {x y : bSet 𝔹} {Γ : 𝔹} (h₁ : Γ ≤ x ⊆ᴮ y) (h₂ : Γ ≤ y ⊆ᴮ x) : Γ ≤ x =ᴮ y :=
begin
  apply bv_have h₂, rw[deduction], apply bv_have h₁, rw[<-deduction],
  ac_change' Γ ⊓ (x ⊆ᴮ y ⊓ y ⊆ᴮ x) ≤ x =ᴮ y, apply inf_le_right_of_le,
  apply eq_of_subset_subset
end

theorem bv_eq_trans {x y z : bSet 𝔹} : (x =ᴮ y ⊓ y =ᴮ z) ≤ x =ᴮ z :=
begin
    induction x with α A B generalizing y z,
    cases y with α' A' B',
    induction z with α'' A'' B'',
    have H1 : ∀ a : α, ∀ a' : α', ∀ a'' : α'',
           (((A a =ᴮ A' a') ⊓ (A' a' =ᴮ A'' a'')) ⊓ B'' a'') ≤ (A a =ᴮ A'' a'' ⊓ B'' a''),
      by {intros a a' a'', refine inf_le_inf _ (by refl), exact @x_ih a (A' a') (A'' a'')},
    have H2 : ∀ i'' : α'', ∀ a' : α', ∀ a : α,
           A'' i'' =ᴮ A' a' ⊓ A' a' =ᴮ A a ⊓ B a ≤ A'' i'' =ᴮ A a ⊓ B a,
      by {intros a'' a' a, refine inf_le_inf _ (by refl),
        convert @x_ih a (A' a') (A'' a'') using 1; simp[bv_eq_symm], ac_refl},
    apply le_inf,
      {bv_intro i, apply deduction.mp,
        change _ ≤ (A i) ∈ᴮ ⟨α'', A'', B''⟩,
       have this1 : ⟨α, A, B⟩ =ᴮ ⟨α', A', B'⟩ ⊓ B i ≤ A i ∈ᴮ ⟨α', A', B'⟩,
       by  {rw[deduction], from inf_le_left_of_le (infi_le _ _)},
       suffices : A i ∈ᴮ ⟨α', A', B'⟩ ⊓ ⟨α', A', B'⟩ =ᴮ ⟨α'', A'', B''⟩ ≤ A i ∈ᴮ ⟨α'', A'', B''⟩,
         by {have := le_trans (inf_le_inf this1 (by refl)) this,
              convert this using 1, ac_refl },
       suffices : ∀ a', ⟨α', A', B'⟩ =ᴮ ⟨α'', A'', B''⟩ ⊓ A i =ᴮ A' a' ⊓ B' a' ≤ A i ∈ᴮ ⟨α'', A'', B''⟩,
         by {convert (supr_le this) using 1, simp[mem, inf_comm, inf_supr_eq],
            congr, ext, ac_refl},
       have this2 : ∀ a', ⟨α', A', B'⟩ =ᴮ ⟨α'', A'', B''⟩ ⊓ B' a' ≤ A' a' ∈ᴮ ⟨α'', A'', B''⟩,
         by {intro a', rw[deduction], apply inf_le_left_of_le, apply infi_le},
       suffices : ∀ a', A i =ᴮ A' a' ⊓ A' a' ∈ᴮ ⟨α'', A'', B''⟩ ≤ A i ∈ᴮ ⟨α'', A'', B''⟩,
         by {intro a', have := le_trans (inf_le_inf (by refl) (this2 a')) (this a'),
         convert this using 1, ac_refl},
       intro a', rw[inf_supr_eq], apply supr_le, intro a'',
       conv {to_lhs, congr, skip, rw[inf_comm]},
       suffices : A i =ᴮ A' a' ⊓ (A' a' =ᴮ A'' a'' ⊓ B'' a'')
         = A i =ᴮ A' a' ⊓ A' a' =ᴮ A'' a'' ⊓ B'' a'',
         by {rw[this], clear this, apply le_trans, exact (H1 i a' a''),
         apply le_supr_of_le a'', rw[inf_comm]},
       ac_refl},
      {bv_intro i'', apply deduction.mp,
        conv {to_rhs, congr, funext, rw[bv_eq_symm]}, change _ ≤ (A'' i'') ∈ᴮ ⟨α, A, B⟩,
        have this1 : ⟨α'', A'', B''⟩ =ᴮ ⟨α', A', B'⟩ ⊓ B'' i'' ≤ A'' i'' ∈ᴮ ⟨α', A', B'⟩,
          by {rw[deduction], apply inf_le_left_of_le, apply infi_le},
        suffices : A'' i'' ∈ᴮ ⟨α', A', B'⟩ ⊓ ⟨α', A', B'⟩ =ᴮ ⟨α, A, B⟩ ≤ A'' i'' ∈ᴮ ⟨α, A, B⟩,
         by {have := le_trans (inf_le_inf this1 (by refl)) this,
              convert this using 1, simp[bv_eq_symm], ac_refl},
        suffices : ∀ a', ⟨α', A', B'⟩ =ᴮ ⟨α, A, B⟩ ⊓ A'' i'' =ᴮ A' a' ⊓ B' a' ≤ A'' i'' ∈ᴮ ⟨α, A, B⟩,
          by {convert (supr_le this) using 1, simp[mem, inf_comm, inf_supr_eq],
            congr, ext, ac_refl},
        have this2 : ∀ a', ⟨α', A', B'⟩ =ᴮ ⟨α, A, B⟩ ⊓ B' a' ≤ A' a' ∈ᴮ ⟨α, A, B⟩,
          by {intro a', rw[deduction], apply inf_le_left_of_le, apply infi_le},
        suffices : ∀ a', A'' i'' =ᴮ A' a' ⊓ A' a' ∈ᴮ ⟨α, A, B⟩ ≤ A'' i'' ∈ᴮ ⟨α, A, B⟩,
          by {intro a', have := le_trans (inf_le_inf (by refl) (this2 a')) (this a'),
         convert this using 1, ac_refl},
        intro a', rw[inf_supr_eq], apply supr_le, intro a,
        conv {to_lhs, congr, skip, rw[inf_comm]},
        suffices : A'' i'' =ᴮ A' a' ⊓ (A' a' =ᴮ A a ⊓ B a)
          = A'' i'' =ᴮ A' a' ⊓ A' a' =ᴮ A a ⊓ B a,
          by {rw[this], clear this, apply le_trans, exact (H2 i'' a' a),
          apply le_supr_of_le a, rw[inf_comm]},
        ac_refl}
end

-- deprecated, do not use
lemma bv_context_symm {Γ : 𝔹} {a₁ a₂ : bSet 𝔹} (H : Γ ≤ a₁ =ᴮ a₂) : Γ ≤ a₂ =ᴮ a₁ := by rwa[bv_eq_symm]

lemma bv_trans {Γ : 𝔹} {a₁ a₂ a₃ : bSet 𝔹} (H₁ : Γ ≤ a₁ =ᴮ a₂) (H₂ : Γ ≤ a₂ =ᴮ a₃) :
  Γ ≤ a₁ =ᴮ a₃ :=
le_trans (le_inf_iff.mpr ⟨H₁,H₂⟩) bv_eq_trans

@[symm]lemma bv_symm {Γ} {x y : bSet 𝔹} (H : Γ ≤ x =ᴮ y) : Γ ≤ y =ᴮ x := by rwa[bv_eq_symm]

lemma bv_rw {x y : bSet 𝔹} (H : x =ᴮ y = ⊤) (ϕ : bSet 𝔹 → 𝔹) {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} : ϕ y = ϕ x :=
begin
  apply le_antisymm, swap, rw[show ϕ x = ϕ x ⊓ ⊤, by simp], rw[<-H, inf_comm], apply h_congr,
  rw[show ϕ y = ϕ y ⊓ ⊤, by simp], rw[<-H, inf_comm, bv_eq_symm], apply h_congr
end

@[instance]def b_setoid (Γ : 𝔹) : setoid (bSet 𝔹) :=
{ r := bv_eq' Γ,
  iseqv := ⟨λ _, bv_refl, λ _ _, bv_symm, λ _ _ _, bv_trans⟩ }

lemma bv_cc.mk_iff {Γ} {x y : bSet 𝔹} : Γ ≤ x =ᴮ y ↔ (@quotient.mk _ (b_setoid Γ) x) = (@quotient.mk _ (b_setoid Γ) y) := by rw [quotient.eq]; refl

lemma bv_cc.mk {Γ} {x y : bSet 𝔹} (H : Γ ≤ x =ᴮ y) : (@quotient.mk _ (b_setoid Γ) x) = (@quotient.mk _ (b_setoid Γ) y) := bv_cc.mk_iff.mp ‹_›

-- TODO(jesse): bundle this into a bv_cc tactic
example {x y z : bSet 𝔹} {Γ : 𝔹} (H1 : Γ ≤ x =ᴮ y) (H2 : Γ ≤ y =ᴮ z) : Γ ≤ x =ᴮ z :=
begin
  replace H1 := bv_cc.mk H1,
  replace H2 := bv_cc.mk H2,
  rw[bv_cc.mk_iff], cc
end
end bSet

namespace tactic
namespace interactive
section bv_cc
open lean.parser lean interactive.types interactive
local postfix `?`:9001 := optional


/--
`apply_at (H : α) F` assumes that F's first explicit argument is of type `α`
and replaces the assumption H with F H.
-/
meta def apply_at (H_tgt : parse ident) (H : parse texpr) : tactic unit :=
 do e_tgt <- resolve_name H_tgt,
    tactic.replace H_tgt ``(%%H %%e_tgt)

meta def apply_all (H : parse texpr) : tactic unit :=
do ctx <- local_context,
   let mk_new_hyp (e : expr) : tactic unit :=
       tactic.try (do n <- get_unused_name, to_expr ``(%%H %%e) >>= note n none)
   in (list.mmap' mk_new_hyp ctx)

meta def bv_cc : tactic unit :=
apply_all ``(bSet.bv_cc.mk) *> `[rw[bSet.bv_cc.mk_iff]] *> cc
   
end bv_cc
end interactive
end tactic

example {α β : Type} (f : α → β) (P : α → Prop) (Q : β → Prop) {a : α} (H : P a) (H' : P a) (C : ∀ {a}, P a → Q (f a)) : true :=
begin
  apply_at H C,
  apply_all C, triv
end

namespace bSet
variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

example {x y z x₁ y₁ z₁: bSet 𝔹} {Γ : 𝔹} (H1 : Γ ≤ x =ᴮ y) (H2 : Γ ≤ y =ᴮ z)
  (H3 : Γ ≤ z =ᴮ z₁) (H4 : Γ ≤ z₁ =ᴮ y₁) (H5 : Γ ≤ y₁ =ᴮ x₁)
: Γ ≤ x =ᴮ x₁ :=
by bv_cc -- :^)

/-- If u = v and u ∈ w, then this implies that v ∈ w -/
lemma subst_congr_mem_left {u v w : bSet 𝔹} : u =ᴮ v ⊓ u ∈ᴮ w ≤ v ∈ᴮ w :=
begin
  simp only [mem_unfold], tidy_context,
  bv_cases_at a_right i, apply bv_use i, bv_split, from le_inf ‹_› (by bv_cc)
end

-- to derive primed versions of lemmas, use poset_yoneda_inv
@[simp]lemma subst_congr_mem_left' {Γ : 𝔹} {u v w : bSet 𝔹} : Γ ≤ u =ᴮ v → Γ ≤ u ∈ᴮ w → Γ ≤ v ∈ᴮ w :=
  λ _ _, poset_yoneda_inv _ subst_congr_mem_left $ le_inf ‹_› ‹_›

-- example {u v w : bSet 𝔹} : u =ᴮ v ⊓ u ∈ᴮ w ≤ v ∈ᴮ w :=
-- begin
--   simp only [mem_unfold], tidy_context,
--   bv_cases_at a_right i, apply bv_use i, bv_split, refine le_inf ‹_› _,
--   from bv_trans (bv_symm a_left) ‹_›
-- end

/-- If v = w and u ∈ v, then this implies that u ∈ w -/
lemma subst_congr_mem_right {u v w : bSet 𝔹} : (v =ᴮ w ⊓ u ∈ᴮ v) ≤ u ∈ᴮ w :=
begin
  induction v, rw[inf_supr_eq], apply supr_le, intro i,
  suffices : mk v_α ‹_› ‹_› =ᴮ w ⊓ v_B i ≤ v_A i ∈ᴮ w,
  have := le_trans (inf_le_inf this (by refl : u =ᴮ v_A i ≤ u =ᴮ v_A i)) _,
  rw[<-inf_assoc], convert this using 1,
  rw[bv_eq_symm, inf_comm], apply subst_congr_mem_left,
  rw[deduction], cases w, apply inf_le_left_of_le, apply infi_le
end

@[simp]lemma subst_congr_mem_right' {Γ : 𝔹} {u v w : bSet 𝔹} : Γ ≤ w =ᴮ v → Γ ≤ u ∈ᴮ w → Γ ≤ u ∈ᴮ v :=
  λ _ _, poset_yoneda_inv _ subst_congr_mem_right $ le_inf ‹_› ‹_›

/- Use rw[bounded_forall] and rw[bounded_exists] to pass from restricted quantifiers to the FOL interpretation of the quantifiers -/
lemma bounded_forall {v : bSet 𝔹} {ϕ : bSet 𝔹 → 𝔹 } {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} :
  (⨅(i_x : v.type), (v.bval i_x ⟹ ϕ (v.func i_x))) = (⨅(x : bSet 𝔹), x ∈ᴮ v ⟹ ϕ x)  :=
begin
  apply le_antisymm,
    {bv_intro x, cases v, simp only with cleanup, rw[supr_imp_eq],
     bv_intro i_y, apply infi_le_of_le i_y,
     rw[<-deduction,<-inf_assoc], apply le_trans, apply inf_le_inf,
     apply bv_imp_elim, refl, rw[inf_comm, bv_eq_symm], apply h_congr},
         {bv_intro i_x', apply infi_le_of_le (func v i_x'), apply imp_le_of_left_le,
     cases v, simp only with cleanup, apply le_supr_of_le i_x',
       apply le_inf, refl, rw[bv_eq_refl], apply le_top}
end

lemma bounded_exists {v : bSet 𝔹} {ϕ : bSet 𝔹 → 𝔹} {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} :
  (⨆(i_x : v.type), (v.bval i_x ⊓ ϕ(v.func i_x))) = (⨆(x : bSet 𝔹), x ∈ᴮ v ⊓ ϕ x) :=
begin
  apply le_antisymm,
    {apply bv_Or_elim, intro i_x, apply bv_use (v.func i_x),
      apply inf_le_inf, apply mem.mk', refl},
    {apply bv_Or_elim, intro x, simp only [mem_unfold],
      apply bv_cases_left, intro i_x, apply bv_use i_x,
      ac_change' bval v i_x ⊓ (x =ᴮ func v i_x ⊓ ϕ x) ≤ bval v i_x ⊓ ϕ (func v i_x),
      apply inf_le_inf, refl, apply h_congr}
end

-- foo_unfold' means that the definition foo will be unfolded using global quantifiers
lemma mem_unfold' {u v : bSet 𝔹} : u ∈ᴮ v = ⨆z, z ∈ᴮ v ⊓ u =ᴮ z :=
by {rw[<-bounded_exists, mem_unfold], intros x y,
    ac_change' y =ᴮ x ⊓ x =ᴮ u ≤ y =ᴮ u,
    simp[bv_eq_symm], exact bv_eq_symm, exact bv_eq_trans }

lemma subset_unfold' {x u : bSet 𝔹} : x ⊆ᴮ u = ⨅(w : bSet 𝔹), w ∈ᴮ x ⟹ w ∈ᴮ u :=
begin
  simp only [subset_unfold], have := @bounded_forall 𝔹 _ x (λ y, y∈ᴮ u),
  dsimp at this, rw[this], intros, apply subst_congr_mem_left
end

theorem mem_ext {x y : bSet 𝔹} {Γ : 𝔹} (h₁ : Γ ≤ ⨅z, z ∈ᴮ x ⟹ z ∈ᴮ y) (h₂ : Γ ≤ ⨅z, z ∈ᴮ y ⟹ z ∈ᴮ x) : Γ ≤ x =ᴮ y :=
by {[smt] eblast_using [subset_ext, subset_unfold']}


@[simp]lemma subset_self_eq_top {x : bSet 𝔹} : x ⊆ᴮ x = ⊤ :=
top_unique subset_self

lemma subset_trans {x y z : bSet 𝔹} : x ⊆ᴮ y ⊓ y ⊆ᴮ z ≤ x ⊆ᴮ z :=
begin
  simp[subset_unfold'], intro i_z, apply bv_specialize_left i_z,
  apply bv_specialize_right i_z, rw[<-deduction],
  ac_change' (i_z ∈ᴮ x ⟹ i_z ∈ᴮ y)  ⊓ i_z ∈ᴮ x ⊓ (i_z ∈ᴮ y ⟹ i_z ∈ᴮ z) ≤ i_z ∈ᴮ z,
  rw[deduction], let H := _, change ((H ⟹ _) ⊓ H : 𝔹) ≤ _,
  apply le_trans, apply bv_imp_elim, rw[<-deduction], rw[inf_comm],
  apply le_trans, apply bv_imp_elim, refl
end

lemma subset_trans' {x y z : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ x ⊆ᴮ y) (H₂ : Γ ≤ y ⊆ᴮ z) : Γ ≤ x ⊆ᴮ z :=
poset_yoneda_inv Γ subset_trans $ le_inf ‹_› ‹_›

-- lemma subset_trans_context {x y z : bSet 𝔹} {c : 𝔹} {h₁ : c ≤ x ⊆ᴮ y} {h₂ : c ≤ y ⊆ᴮ z} : c ≤ x ⊆ᴮ z :=
-- begin
--   apply bv_have h₂, rw[deduction], apply bv_have h₁, rw[<-deduction],
--   ac_change' c ⊓ (x ⊆ᴮ y ⊓ y ⊆ᴮ z) ≤ x ⊆ᴮ z, apply inf_le_right_of_le,
--   apply subset_trans
-- end

lemma mem_of_mem_subset {x y z : bSet 𝔹} {Γ} (H₂ : Γ ≤ y ⊆ᴮ z) (H₁ : Γ ≤ x ∈ᴮ y) : Γ ≤ x ∈ᴮ z :=
by {rw[subset_unfold'] at H₂, from H₂ x ‹_›}

-- lemma bounded_forall' {ϕ : bSet 𝔹 → 𝔹 } {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} {v : bSet 𝔹} :
--   (⨅(i_x : v.type), (v.bval i_x ⟹ ϕ (v.func i_x))) = (⨅(x : bSet 𝔹), x ∈ᴮ v ⟹ ϕ x)  :=
-- begin
--   apply le_antisymm,
--     {bv_intro x, cases v, simp, rw[supr_imp_eq],
--      bv_intro i_y, apply infi_le_of_le i_y,
--      rw[<-deduction,<-inf_assoc], apply le_trans, apply inf_le_inf,
--      apply bv_imp_elim, refl, rw[inf_comm, bv_eq_symm], apply h_congr},
--          {bv_intro i_x', apply infi_le_of_le (func v i_x'), apply imp_le_of_left_le,
--      cases v, simp, apply le_supr_of_le i_x',
--        apply le_inf, refl, rw[bv_eq_refl], apply le_top}
-- end


lemma subst_congr_subset_left {x v u} : ((v ⊆ᴮ u) ⊓ (x =ᴮ v) : 𝔹) ≤ (x ⊆ᴮ u) :=
begin
  simp only [subset_unfold],
  have H₁ := @bounded_forall _ _ v (λ x, x ∈ᴮ u)
    (by {intros, apply subst_congr_mem_left}),
  have H₂ := @bounded_forall _ _ x (λ x, x ∈ᴮ u)
    (by {intros, apply subst_congr_mem_left}),
  rw[H₁, H₂], dsimp, bv_intro z, rw[deduction],
  apply infi_le_of_le z, rw[<-deduction, <-deduction], rw[inf_assoc],
  apply le_trans, apply inf_le_inf, refl, apply subst_congr_mem_right,
  apply bv_imp_elim -- todo write tactics to make these calculations easier
end

lemma subst_congr_subset_right {x v u} : ((v ⊆ᴮ u) ⊓ (u =ᴮ x) : 𝔹) ≤ (v ⊆ᴮ x) :=
begin
  simp only [subset_unfold], bv_intro j, apply bv_specialize_left j,
  rw[<-deduction], ac_change' ((bval v j ⟹ func v j ∈ᴮ u) ⊓ bval v j) ⊓  u =ᴮ x ≤ func v j ∈ᴮ x,
  rw[deduction], apply le_trans, apply bv_imp_elim, rw[<-deduction, inf_comm],
  apply subst_congr_mem_right
end

-- TODO(jesse) maybe replace this with typeclasses instead?
@[reducible]def B_ext (ϕ : bSet 𝔹 → 𝔹) : Prop :=
  ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y

@[simp]lemma B_ext_bv_eq_left {y : bSet 𝔹} : B_ext (λ x, x =ᴮ y) :=
by {unfold B_ext, intros, rw[bv_eq_symm], apply bv_eq_trans}

@[simp]lemma B_ext_bv_eq_right {x : bSet 𝔹} : B_ext (λ y, x =ᴮ y) :=
by {unfold B_ext, intros, rw[inf_comm], apply bv_eq_trans}

@[simp]lemma B_ext_mem_left {y : bSet 𝔹} : B_ext (λ x, x ∈ᴮ y) :=
by unfold B_ext; intros; apply subst_congr_mem_left

@[simp]lemma B_ext_mem_right {x : bSet 𝔹} : B_ext (λ y, x ∈ᴮ y) :=
by unfold B_ext; intros; apply subst_congr_mem_right

@[simp]lemma B_ext_subset_left {y : bSet 𝔹} : B_ext (λ x, x ⊆ᴮ y) :=
by {unfold B_ext, intros, rw[inf_comm, bv_eq_symm], apply subst_congr_subset_left}

@[simp]lemma B_ext_subset_right {x : bSet 𝔹} : B_ext (λ y, x ⊆ᴮ y) :=
by {unfold B_ext, intros, rw[inf_comm], apply subst_congr_subset_right}

@[simp]lemma B_ext_sup {ϕ₁ ϕ₂ : bSet 𝔹 → 𝔹} {h₁ : B_ext ϕ₁} {h₂ : B_ext ϕ₂} :
  B_ext (λ x, ϕ₁ x ⊔ ϕ₂ x) :=
begin
  intros x y, dsimp, rw[inf_comm, deduction], apply bv_or_elim;
  apply bv_imp_intro; [apply le_sup_left_of_le, apply le_sup_right_of_le];
  rw[inf_comm]; [apply h₁, apply h₂]
end

@[simp]lemma B_ext_inf {ϕ₁ ϕ₂ : bSet 𝔹 → 𝔹} (h₁ : B_ext ϕ₁) (h₂ : B_ext ϕ₂) :
  B_ext (λ x, ϕ₁ x ⊓ ϕ₂ x) :=
begin
  intros x y, dsimp, apply le_inf,
  transitivity x =ᴮ y ⊓ ϕ₁ x,
    by {apply inf_le_inf, refl, apply inf_le_left},
    apply h₁,
  transitivity x =ᴮ y ⊓ ϕ₂ x,
    by {apply inf_le_inf, refl, apply inf_le_right},
    apply h₂
end

@[simp]lemma B_ext_imp {ϕ₁ ϕ₂ : bSet 𝔹 → 𝔹} {h₁ : B_ext ϕ₁} {h₂ : B_ext ϕ₂} :
  B_ext (λ x, ϕ₁ x ⟹ ϕ₂ x) :=
begin
  unfold B_ext, intros x y, rw[<-deduction],
  ac_change' x =ᴮ y ⊓  ϕ₁ y ⊓ (ϕ₁ x ⟹ ϕ₂ x) ≤ ϕ₂ y,
  rw[deduction], rw[bv_eq_symm], apply le_trans', apply h₁, rw[<-deduction, inf_comm],
  ac_change' (ϕ₁ x ⟹ ϕ₂ x)  ⊓ ϕ₁ x ⊓ (y =ᴮ x ⊓ ϕ₁ y) ≤ ϕ₂ y, rw[deduction],
  apply le_trans, apply bv_imp_elim, rw[<-deduction], rw[<-inf_assoc],
  apply inf_le_left_of_le, rw[inf_comm, bv_eq_symm], apply h₂
end

@[simp]lemma B_ext_const {b : 𝔹} : B_ext (λ x, b) :=
by tidy

@[simp]lemma B_ext_neg {ϕ₁ : bSet 𝔹 → 𝔹} {h : B_ext ϕ₁} : B_ext (λ x, - ϕ₁ x) :=
by {simp only [imp_bot.symm], apply B_ext_imp, simpa, from B_ext_const}

@[simp]lemma B_ext_infi {ι : Type*} {Ψ : ι → (bSet 𝔹 → 𝔹)} {h : ∀ i, B_ext $ Ψ i} : B_ext (λ x, ⨅i, Ψ i x) :=
by {intros x y, dsimp, bv_intro i, apply bv_specialize_right i, apply h}

@[simp]lemma B_ext_supr {ι : Type*} {ψ : ι → (bSet 𝔹 → 𝔹)} {h : ∀i, B_ext $ ψ i} : B_ext (λ x, ⨆i, ψ i x) :=
by {intros x y, dsimp, apply bv_cases_right, intro i, apply bv_use i, apply h}

example {y : bSet 𝔹} : B_ext (λ x : bSet 𝔹, x ∈ᴮ y ⊔ y ∈ᴮ x) := by change B_ext _; simp

-- use for rewriting the goal with the first argument
lemma bv_rw' {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x =ᴮ y) {ϕ : bSet 𝔹 → 𝔹} {h_congr : B_ext ϕ} {H_new : Γ ≤ ϕ y} : Γ ≤ ϕ x :=
begin
  have : Γ ≤ y =ᴮ x ⊓ ϕ y,
    by {apply le_inf, rw[bv_eq_symm], from ‹_›, from ‹_›},
  from (poset_yoneda_inv _ (h_congr _ _) this)
end

meta def H_congr_handler : tactic unit := `[simp]

-- use for rewriting in the second argument using the first
lemma bv_rw'' {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x =ᴮ y) {ϕ : bSet 𝔹 → 𝔹} (H_new : Γ ≤ ϕ x) (h_congr : B_ext ϕ . H_congr_handler) : Γ ≤ ϕ y :=
begin
  have : Γ ≤ x =ᴮ y ⊓ ϕ x,
    by {apply le_inf, from ‹_›, from ‹_›},
  from (poset_yoneda_inv _ (h_congr _ _) this)
end

lemma mem_congr {Γ : 𝔹} {x₁ x₂ y₁ y₂ : bSet 𝔹} {H₁ : Γ ≤ x₁ =ᴮ y₁} {H₂ : Γ ≤ x₂ =ᴮ y₂} {H₃ : Γ ≤ x₁ ∈ᴮ x₂} :
  Γ ≤ y₁ ∈ᴮ y₂ :=
by {rw[bv_eq_symm] at H₁ H₂, apply bv_rw' H₁, simp, apply bv_rw' H₂, simpa}

def is_definite (u : bSet 𝔹) : Prop := ∀ i : u.type, u.bval i = ⊤

lemma eq_empty {u : bSet 𝔹} : u =ᴮ ∅ = -⨆i, u.bval i :=
begin
  simp only [bv_eq_unfold], simp only [mem_unfold],
  simp only [inf_top_eq, bSet.forall_over_empty, bSet.exists_over_empty,imp_bot, neg_supr]
end

@[simp]lemma empty_subset {x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ ∅ ⊆ᴮ x :=
by rw[subset_unfold]; bv_intro; repeat{cases i}

lemma empty_spec {x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ -(x ∈ᴮ ∅) := by simp[mem_unfold]

lemma bot_of_mem_empty {x : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x ∈ᴮ ∅) : Γ ≤ ⊥ :=
by {have := @empty_spec 𝔹 _ x Γ, rw[<-imp_bot] at this, from this H}

@[simp]lemma subst_congr_insert1_left {u w v : bSet 𝔹} : u =ᴮ w ≤ bSet.insert1 u v =ᴮ bSet.insert1 w v :=
begin
  rcases v with ⟨α,A,B⟩, simp[bSet.insert1], split; intro i; apply bv_imp_intro;
  refine le_sup_right_of_le _; apply bv_use i; rw[inf_comm]; simp
end

@[simp]lemma subst_congr_insert1_left' {u w v : bSet 𝔹} {c : 𝔹} {h : c ≤ u =ᴮ w} : c ≤ bSet.insert1 u v =ᴮ bSet.insert1 w v :=
by apply le_trans h; simp

@[simp]lemma subst_congr_insert1_left'' {u w v : bSet 𝔹} {c : 𝔹} {h : c ≤ u =ᴮ w} : c ≤ {v, u} =ᴮ {v, w} :=
  by {unfold has_insert.insert, apply subst_congr_insert1_left', from ‹_›}

@[simp]lemma subst_congr_insert1_right {u w v : bSet 𝔹} : u=ᴮw ≤ bSet.insert1 v u =ᴮ bSet.insert1 v w :=
by {rcases u with ⟨α,A,B⟩, rcases w with ⟨α',A',B'⟩, simp[bSet.insert1]; split; intro i; apply bv_imp_intro,
    apply le_sup_right_of_le, apply le_trans, apply inf_le_inf, refl, apply mem.mk, from A, change _ ≤ A i ∈ᴮ ⟨α',A',B'⟩,
    apply subst_congr_mem_right,
    apply le_sup_right_of_le, apply le_trans, apply inf_le_inf, refl, apply mem.mk, from A', conv {to_rhs, congr, funext,rw[bv_eq_symm]},
    change _ ≤ A' i ∈ᴮ ⟨α,A,B⟩, rw[bv_eq_symm], apply subst_congr_mem_right}

@[simp]lemma subst_congr_insert1_right' {u w v : bSet 𝔹} {c : 𝔹} {h : c ≤ u =ᴮ w} : c ≤ bSet.insert1 v u =ᴮ bSet.insert1 v w :=
by {apply le_trans h, apply subst_congr_insert1_right}

@[simp]lemma subst_congr_insert1_right'' {u w v : bSet 𝔹} {c : 𝔹} {h : c ≤ u =ᴮ w} : c ≤ {u,v} =ᴮ {w,v} :=
  by {unfold has_insert.insert, apply subst_congr_insert1_right', apply subst_congr_insert1_left', from ‹_›}

/- some singleton lemmas -/

@[simp]lemma eq_singleton_of_eq {x y : bSet 𝔹} {c : 𝔹} {h : c ≤ x =ᴮ y} : c ≤ {x} =ᴮ {y} :=
by {apply subst_congr_insert1_left', from ‹_›}

lemma eq_of_eq_singleton {x y : bSet 𝔹} {c : 𝔹} {h : c ≤ {x} =ᴮ {y}} : c ≤ x =ᴮ y :=
begin
  apply le_trans h, simp[singleton, has_insert.insert], simp only [insert1_unfold],
  simp only [bv_eq_unfold],
  simp only [lattice.le_inf_iff, lattice.infi_option, lattice.inf_top_eq,
 bSet.mem, lattice.top_inf_eq, lattice.supr_option, lattice.top_imp, lattice.sup_bot_eq,
 lattice.le_infi_iff, bSet.forall_over_empty, bSet.exists_over_empty] with cleanup,
  split; intro i; [apply inf_le_left_of_le, apply inf_le_right_of_le];
  rw[bv_eq_unfold]; apply inf_le_left_of_le; apply bv_specialize i; refl
end

lemma eq_singleton_iff_eq {x y : bSet 𝔹} {c : 𝔹} : c ≤ {x} =ᴮ {y} ↔ c ≤ x =ᴮ y :=
by {split; intros; [apply eq_of_eq_singleton, apply eq_singleton_of_eq]; from ‹_›}

lemma singleton_unfold {x : bSet 𝔹} : {x} = bSet.insert1 x ∅ := rfl

@[simp]lemma singleton_type {x : bSet 𝔹} : type ({x} : bSet 𝔹) = option (ulift _root_.empty) := rfl

@[simp]lemma singleton_func {x : bSet 𝔹} {o} : func ({x} : bSet 𝔹) o = option.rec_on o x (empty.elim ∘ ulift.down) := rfl

@[simp]lemma singleton_bval {x : bSet 𝔹} {o} : bval ({x} : bSet 𝔹) o = option.rec_on o ⊤ (empty.elim ∘ ulift.down) := rfl

@[simp]lemma singleton_bval_none {x : bSet 𝔹} : bval ({x} : bSet 𝔹) none = ⊤ := rfl

-- @[simp]lemma eq_of_eq_insert_right {u w v : bSet 𝔹} {c : 𝔹} {h : c ≤ bSet.insert1 v u =ᴮ bSet.insert1 v w} : c ≤ u =ᴮ w :=
-- begin
--   apply le_trans h, simp only [insert1_unfold, bv_eq_unfold], simp, split; intro i; [apply inf_le_left_of_le, apply inf_le_right_of_le],
--   {apply bv_specialize i, apply bv_cancel_antecedent, apply bv_or_elim, },
--   {sorry}
-- end

/-- ϕ (x) is true if and only if the Boolean truth-value of ϕ(x̌) is ⊤-/
/- To even state this theorem, we need to set up more general machinery for
   Boolean-valued structures and the interpretation of formulas within them -/
-- theorem check_transfer : sorry := sorry

def mixture {ι : Type u} (a : ι → 𝔹) (u : ι → bSet 𝔹) : bSet 𝔹 :=
  ⟨Σ(i : ι), (u i).type,
    λx, (u x.fst).func x.snd,
      λx, ⨆(j:ι), a j ⊓ ((u x.fst).func x.snd) ∈ᴮ u j⟩

/-- Given a₁ a₂ : 𝔹, return the canonical map from ulift bool to 𝔹 given by ff ↦ a₁ and tt ↦ a₂-/
@[reducible]def bool.map {α : Type*} (a₁ a₂ : α) : (ulift bool) → α :=
  λ x, bool.rec_on (x.down) a₁ a₂

def two_term_mixture (a₁ a₂ : 𝔹) (h_anti : a₁ ⊓ a₂ = ⊥) (u₁ u₂ : bSet 𝔹) : bSet 𝔹 :=
@mixture 𝔹 _ (ulift bool) (bool.map a₁ a₂) (bool.map u₁ u₂)

-- @[simp]lemma two_term_mixture_type (a₁ a₂ : 𝔹) (h_anti : a₁ ⊓ a₂ = ⊥) (u₁ u₂ : bSet 𝔹) :
--   (two_term_mixture a₁ a₂ h_anti u₁ u₂).type = (Σ(i : ulift bool), ((bool.map u₁ u₂) i).type) := sorry

lemma two_term_mixture_h_star (a₁ a₂ : 𝔹) (h_anti : a₁ ⊓ a₂ = ⊥) (u₁ u₂ : bSet 𝔹) :
  ∀ i j : (ulift bool), (bool.map a₁ a₂) i ⊓ (bool.map a₁ a₂) j ≤ (bool.map u₁ u₂) i =ᴮ (bool.map u₁ u₂) j :=
begin
  intros i j, cases i, cases j, cases i; cases j; try{simp*},
  change a₂ ⊓ a₁ ≤ _, rw[inf_comm, h_anti], apply bot_le
end

@[simp]lemma bval_mixture {ι : Type u} {a : ι → 𝔹} {u : ι → bSet 𝔹} :
  (mixture a u).bval = λx, ⨆(j:ι), a j ⊓ ((u x.fst).func x.snd) ∈ᴮ u j :=
  by refl

@[simp]lemma two_term_mixture_bval (a₁ a₂ : 𝔹) (h_anti : a₁ ⊓ a₂ = ⊥) (u₁ u₂ : bSet 𝔹) : ∀ i,
  (two_term_mixture a₁ a₂ h_anti u₁ u₂).bval i = (a₁ ⊓ ((two_term_mixture a₁ a₂ h_anti u₁ u₂).func i ∈ᴮ u₁)) ⊔ (a₂ ⊓ ((two_term_mixture a₁ a₂ h_anti u₁ u₂).func i ∈ᴮ u₂)) := λ i,
begin
  dsimp[two_term_mixture], tidy, apply le_antisymm, apply supr_le, intro j, repeat{cases j},
  apply le_sup_left_of_le, refl, apply le_sup_right_of_le, refl,
  apply bv_or_elim; [apply bv_use (ulift.up ff), apply bv_use (ulift.up tt)]; refl
end

def floris_mixture {ι : Type u} (a : ι → 𝔹) (u : ι → bSet 𝔹) : bSet 𝔹 :=
  ⟨Σ(i : ι), (u i).type, λx, (u x.fst).func x.snd, λx, a x.fst ⊓ (u x.fst).bval x.snd⟩

/-- Mixing lemma, c.f. Bell's book or Lemma 1 of Hamkins-Seabold -/
lemma mixing_lemma' {ι : Type u} (a : ι → 𝔹) (τ : ι → bSet 𝔹) (h_star : ∀ i j : ι, a i ⊓ a j ≤ τ i =ᴮ τ j) : ∀ i : ι, a i ≤ (mixture a τ) =ᴮ τ i := λ i,
begin
rw[bv_eq_unfold],
  apply le_inf,
    {bv_intro i_z, apply bv_imp_intro,
    simp only [bSet.bval, bSet.mem, bSet.func, bSet.type, bSet.bval_mixture],
    rw[inf_supr_eq], apply bv_Or_elim,
    intro j, rw[<-inf_assoc],
    have : a i ⊓ a j ⊓ func (τ (i_z.fst)) (i_z.snd) ∈ᴮ τ j ≤ (τ i =ᴮ τ j) ⊓ func (τ (i_z.fst)) (i_z.snd) ∈ᴮ τ j,
      by {apply inf_le_inf (h_star i j), refl},
    apply le_trans this, rw[bv_eq_symm], apply subst_congr_mem_right},
  {bv_intro i_z, rw[<-deduction], refine le_supr_of_le (sigma.mk i i_z) _,
  simp only [bv_eq_top_of_eq, mem, type, inf_top_eq, bval, func],
  refine le_supr_of_le i _, refine inf_le_inf (by refl : a i ≤ a i) _, dsimp only,
  cases (τ i), refine le_supr_of_le i_z _, from le_inf (by refl) (by simp)}
end

lemma mixing_lemma {ι : Type u} (a : ι → 𝔹) (τ : ι → bSet 𝔹) (h_star : ∀ i j : ι, a i ⊓ a j ≤ τ i =ᴮ τ j) : ∃ x, ∀ i : ι, a i ≤ x =ᴮ τ i :=
 by refine ⟨mixture a τ, λ i, _⟩; apply mixing_lemma'; assumption

lemma mixing_lemma_two_term (a₁ a₂ : 𝔹) (h_anti : a₁ ⊓ a₂ = ⊥) (u₁ u₂ : bSet 𝔹) :
  a₁ ≤ (two_term_mixture a₁ a₂ h_anti u₁ u₂ =ᴮ u₁) ∧ a₂ ≤ (two_term_mixture a₁ a₂ h_anti u₁ u₂ =ᴮ u₂) :=
begin
  have := mixing_lemma' (bool.map a₁ a₂) (bool.map u₁ u₂)
    (by {apply two_term_mixture_h_star, exact h_anti}),
  split; [specialize this (ulift.up ff), specialize this (ulift.up tt)]; exact this
end

-- TODO(jesse) try proving mixing_lemma with floris_mixture and see if anything goes wrong

/-- In particular, the mixing lemma applies when the weights (a_i) form an antichain and the indexing is injective -/
lemma h_star_of_antichain_injective {ι : Type u} {a : ι → 𝔹} {τ : ι → bSet 𝔹} {h_anti : antichain (a '' set.univ)} {h_inj : function.injective a} :
  ∀ i j : ι, a i ⊓ a j ≤ τ i =ᴮ τ j :=
begin
  intros i j, by_cases a i = a j, simp[h_inj h],
  have := h_anti _ _ _ _ h, simp[this], tidy
end

/- Note: this is the special condition assumed of indexed antichains by Bell-/
lemma h_star_of_antichain_index {ι : Type u} {a : ι → 𝔹} {τ : ι → bSet 𝔹} {h_anti : antichain (a '' set.univ)} {h_index : ∀ i j : ι, i ≠ j → a i ⊓ a j = ⊥} :
  ∀ i j : ι, a i ⊓ a j ≤ τ i =ᴮ τ j :=
  λ i j, by {haveI : decidable_eq ι := λ _ _,
  by apply classical.prop_decidable _,
    by_cases i = j, simp[h], finish[h_index i j]}

/- The next two lemmas use the fact that 𝔹 : Type u to extract a small set witnessing quantification over all of bSet 𝔹 -/

/- i.e., in bSet 𝔹, any existential quantification is equivalent to a bounded existential quantification. this is one place where it's crucial that 𝔹 lives in the type universe out of which bSet 𝔹 is being built -/
section smallness
variable {ϕ : bSet 𝔹 → 𝔹}

@[reducible, simp]noncomputable def fiber_lift (b : ϕ '' set.univ) :=
classical.indefinite_description (λ a : bSet 𝔹, ϕ a = b.val) $
  by {cases b.property, use w, exact h.right}

noncomputable def B_small_witness : bSet 𝔹 :=
⟨ϕ '' set.univ, λ b, (fiber_lift b).val, λ _, ⊤⟩

@[simp]lemma B_small_witness_spec : ∀ b, ϕ ((@B_small_witness _ _ ϕ).func b) = b.val :=
  λ b, (fiber_lift b).property

lemma B_small_witness_supr : (⨆(x : bSet 𝔹), ϕ x) = ⨆(b : (@B_small_witness _ _ ϕ).type), ϕ (B_small_witness.func b) :=
begin
 apply le_antisymm,
 apply supr_le, intro x, let b : type B_small_witness :=
   by {use ϕ x, simp only [set.image_univ, set.mem_range], exact ⟨x, rfl⟩},
 fapply le_supr_of_le, exact b, have := B_small_witness_spec b, dsimp at this, rw[this],
 apply supr_le, intro b, apply le_supr_of_le, swap, exact (fiber_lift b).val, refl
end

@[reducible, simp]def not_b (b : 𝔹) : set 𝔹 := λ y, y ≠ b

section well_ordering
variables {α : Type*} (r : α → α → Prop) [is_well_order α r]
local infix `≺`:50 := r

def down_set (a : α) : set α := {a' | a' ≺ a}

def down_set' (a : α) : set α := insert a $ down_set r a

lemma down_set_trans {a b} {h : a ≺ b} : down_set r a ⊆ down_set r b :=
begin
  intros x H, have := is_well_order.is_trans r, cases this, apply this,
  exact H, exact h
end

end well_ordering

variable (r : type (@B_small_witness _ _ ϕ) → type (@B_small_witness _ _ ϕ) → Prop)
variable [is_well_order _ r]
local infix `≺`:50 := r

lemma down_set_mono_supr {a b} {h : a ≺ b} {s : type (@B_small_witness _ _ ϕ) → 𝔹} :
 (⨆(i ∈ down_set r a), s i) ≤ (⨆(i ∈ down_set r b), s i) :=
begin
  apply supr_le_supr, intro i, apply supr_le, intro H, apply le_supr_of_le,
  apply down_set_trans, exact h, exact H, refl
end

lemma down_set'_mono_supr {a b} {h : a ≺ b} {s : type (@B_small_witness _ _ ϕ) → 𝔹} :
 (⨆(i ∈ down_set' r a), s i) ≤ (⨆(i ∈ down_set' r b), s i) :=
begin
  apply supr_le_supr, intro i, apply supr_le, intro H,
 apply le_supr_of_le,
  cases H, apply or.inr, rw[H], exact h, apply or.inr,
  apply down_set_trans, exact h, exact H, refl
end

def witness_antichain : _ → 𝔹 :=
(λ b : type (@B_small_witness _ _ ϕ), b.val - (⨆(b' : (down_set r b)), b'.val.val))

def trichotomy := (is_well_order.is_trichotomous r).trichotomous

lemma dichotomy_of_neq (x y) : x ≠ y → x ≺ y ∨ y ≺ x :=
λ H, by {[smt] eblast_using [trichotomy r x y]}

lemma not_ge_of_in_down_set (a b) : a ∈ down_set r b → ¬ b ≺ a :=
begin
  intros H H', have H'' : a ≺ b, by {simpa[down_set]},
  cases (show (is_asymm _ r), by apply_instance),
  specialize asymm a b H'', contradiction
end

--TODO(jesse) clean this up later, maybe write ac_transpose?
-- run_cmd mk_simp_attr `reassoc
-- @[reassoc]lemma sup_reassoc {a b c : 𝔹} : a ⊔ (b ⊔ c) = a ⊔ b ⊔ c :=
-- by ac_refl

-- @[reassoc]lemma inf_reassoc {a b c : 𝔹} : a ⊓ (b ⊓ c) = a ⊓ b ⊓ c :=
-- by ac_refl

-- @[reassoc]lemma abcd_reassoc_sup {a b c d : 𝔹} : (a ⊔ b) ⊔ (c ⊔ d) = a ⊔ b ⊔ c ⊔ d :=
-- by rw[sup_reassoc]

-- @[reassoc]lemma abcd_reassoc_inf {a b c d : 𝔹} : (a ⊓ b) ⊓ (c ⊓ d) = a ⊓ b ⊓ c ⊓ d :=
-- by rw[inf_reassoc]

-- lemma abcd_rw_cabd_sup {a b c d : 𝔹} : a ⊔ b ⊔ c ⊔ d = c ⊔ b ⊔ a ⊔ d :=
-- by ac_refl

-- lemma abcd_rw_cabd_inf {a b c d : 𝔹} : a ⊓ b ⊓ c ⊓ d = c ⊓ b ⊓ a ⊓ d :=
-- by ac_refl

-- lemma abcd_rw_bcad_inf {a b c d : 𝔹} : a ⊓ b ⊓ c ⊓ d = b ⊓ c ⊓ a ⊓ d :=
-- by ac_refl

def witness_antichain_index : ∀ {i j}, i ≠ j → (@witness_antichain _ _ ϕ r _) i ⊓ (@witness_antichain _ _ ϕ r _) j = ⊥ :=
λ x y h_neq,
begin
  dsimp[witness_antichain], simp[sub_eq, neg_supr],
  apply bot_unique, cases dichotomy_of_neq r _ _ h_neq,
  {/- `tidy_context` says -/ apply poset_yoneda, intros Γ a,
    simp only [le_inf_iff] at *, cases a, cases a_right, cases a_left,
     replace a_right_right := a_right_right ⟨x,‹_›⟩, dsimp at a_right_right,
     bv_contradiction},
  { /- `tidy_context` says -/ apply poset_yoneda, intros Γ a,
    simp only [le_inf_iff] at *, cases a, cases a_right, cases a_left,
     replace a_left_right := a_left_right ⟨y,‹_›⟩, dsimp at a_left_right,
     bv_contradiction}
end

lemma witness_antichain_antichain : antichain ((@witness_antichain _ _ ϕ r _) '' set.univ) :=
begin
  intros x h_x y h_y h_neq, simp at h_x h_y, rcases h_y with ⟨w_y, h_y⟩,
  rcases h_x with ⟨w_x, h_x⟩, rw[<-h_y, <-h_x],
  apply witness_antichain_index, by_contra, cc
end

lemma witness_antichain_property : ∀ b, (@witness_antichain _ _ ϕ r _) b ≤ b.val :=
  λ b, by simp[witness_antichain, sub_eq]

lemma supr_antichain2_contains : (⨆ (b' : type (@B_small_witness _ _ ϕ)), ϕ (func (@B_small_witness _ _ ϕ) b')) ≤
    ⨆ (b : type (@B_small_witness _ _ ϕ)), witness_antichain r b :=
begin
  apply supr_le, intro i, apply le_supr_of_le'', fsplit,
  exact down_set' r i, rw[B_small_witness_spec i],
  have := (is_well_order.wf r).apply i, induction this,
  intros,
 rw[down_set',supr_insert], unfold witness_antichain,
  rw[sub_eq], rw[sup_inf_right], apply le_inf, apply le_sup_left,
  -- simp[neg_supr, sub_eq],
  apply le_trans (@le_top _ _ this_x.val),
     let A := _, change ⊤ ≤ (A ⊔ _ : 𝔹), apply le_trans (by simp : ⊤ ≤ A ⊔ -A), apply sup_le_sup, refl, dsimp[A],
   rw[lattice.neg_neg],
   apply supr_le, intro j,
   apply le_trans (this_ih j j.property), unfold witness_antichain,
   apply supr_le_supr, intro i', apply supr_le, intro H',
   cases H', subst H', apply le_supr_of_le, exact j.property, refl,
   apply le_supr_of_le, apply down_set_trans, exact j.property, exact H',
   refl
end
end smallness


lemma maximum_principle (ϕ : bSet 𝔹 → 𝔹) (h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y) : ∃ u, (⨆(x:bSet 𝔹), ϕ x) = ϕ u :=
begin
  have := classical.indefinite_description _ (@well_ordering_thm (type (@B_small_witness _ _ ϕ))),
  cases this with r inst_r,
  haveI : is_well_order _ r := by assumption,
  let w := @B_small_witness _ _ ϕ,
    have from_mixing_lemma := mixing_lemma ((witness_antichain r)) (w.func)
      (λ i j, by {by_cases i = j, finish, simp[witness_antichain_index r h]}),
    rcases from_mixing_lemma with ⟨u, H_w⟩,
    use u, fapply le_antisymm,
    {rw[B_small_witness_supr],
     have H1 : (⨆(b : type B_small_witness), (witness_antichain r) b) ≤ ϕ u,
     apply supr_le, intro ξ,
    have this'' : ∀ b, (witness_antichain r) b ≤ u =ᴮ func w b ⊓ b.val,
      by {intro b, apply le_inf, apply H_w b, apply witness_antichain_property},
    have this''' : ∀ b, u =ᴮ func w b ⊓ (ϕ (func B_small_witness b)) ≤ ϕ u,
      intro b, dsimp[w], rw[bv_eq_symm], apply h_congr, apply le_trans,
      exact this'' ξ, convert this''' ξ, apply (B_small_witness_spec _).symm,
   suffices H2 : (⨆(b' : type (@B_small_witness _ _ ϕ)), ϕ (func B_small_witness b')) ≤ ⨆(b : type (@B_small_witness _ _ ϕ)), (witness_antichain r) b,
   from le_trans H2 H1, apply supr_antichain2_contains},
    {apply le_supr}
end

lemma maximum_principle_verbose {ϕ : bSet 𝔹 → 𝔹} {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} {b : 𝔹} (h_eq_top L : (⨆(x:bSet 𝔹), ϕ x) = b) : ∃ u, ϕ u = b :=
 by cases maximum_principle ϕ h_congr with w h; from ⟨w, by finish⟩

/-- "∃ x ∈ u, ϕ x implies ∃ x : bSet 𝔹, ϕ x", but this time, say it in Boolean -/
lemma weaken_ex_scope {α : Type*} (A : α → bSet 𝔹) (ϕ : bSet 𝔹 → 𝔹)  : (⨆(a : α), ϕ (A a)) ≤ (⨆(x : bSet 𝔹), ϕ x) :=
supr_le $ λ a, le_supr_of_le (A a) (by refl)

lemma maximum_principle_bounded_top {ϕ : bSet 𝔹 → 𝔹} {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} {α : Type*} {A : α → bSet 𝔹} (h_eq_top : (⨆(a:α), ϕ (A a)) = ⊤) : ∃ u, ϕ u = ⊤ :=
@maximum_principle_verbose 𝔹 (by apply_instance) ϕ h_congr ⊤ (by {have := weaken_ex_scope A ϕ, finish}) (by {have := weaken_ex_scope A ϕ, finish})

/-- Convert a Boolean-valued ∀∃-statement into a Prop-valued ∀∃-statement
  Given A : α → bSet 𝔹, a binary function ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹, a truth-value assignment
  B : α → 𝔹, ∀ i : α, there exists a y_i : bSet 𝔹, such that
  (B i ⟹ ϕ (A i) y_i) ≥ ⨅(i:α), B i ⟹ ⨆(y : bSet 𝔹), ϕ(A i, bSet 𝔹)

  A more verbose, but maybe clearer way to see this is:
  if there is an equality (⨅i-⨆j body i j) = b,
  then for all i, there exists j, such that body i j ≥ b

  This is a consequence of the maximum principle.
-/
lemma AE_convert {α 𝔹 : Type*} [nontrivial_complete_boolean_algebra 𝔹] (A : α → bSet 𝔹)
  (B : α → 𝔹) (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹) (h_congr : ∀ x y z, x =ᴮ y ⊓ ϕ z x ≤ ϕ z y) :
  ∀ i : α, ∃ y : bSet 𝔹, (⨅(j:α), (B j ⟹ ⨆(z : bSet 𝔹), ϕ (A j) z)) ≤ (B i ⟹ ϕ (A i) y) :=
λ i,
  by {have := maximum_principle (λ y, ϕ (A i) y)
                (by {intros x y, apply h_congr}),
      rcases this with ⟨u', H'⟩, use u', apply infi_le_of_le i,
      apply imp_le_of_right_le, from le_of_eq H'}

section mixing_corollaries
-- The lemmas in this section are corollaries of the mixing lemma
variables (X u₁ u₂ : bSet 𝔹) (a₁ a₂ : 𝔹) (h_anti : a₁ ⊓ a₂ = ⊥) (h_partition : a₁ ⊔ a₂ = ⊤)

include h_partition
lemma two_term_mixture_mem_top (h₁ : u₁ ∈ᴮ X = ⊤) (h₂ : u₂ ∈ᴮ X = ⊤) :
  two_term_mixture a₁ a₂ h_anti u₁ u₂ ∈ᴮ X = ⊤:=
begin
  let U := _, change U ∈ᴮ X= _, apply top_unique,
  have : ⊤ ≤ U =ᴮ u₁ ⊔ U =ᴮ u₂,
    by {rw[h_partition.symm],
       have := mixing_lemma_two_term a₁ a₂ h_anti u₁ u₂,apply sup_le_sup, tidy},
  have : ⊤ ≤ (U =ᴮ u₁ ⊔ U =ᴮ u₂) ⊓ (u₁ ∈ᴮ X ⊓ u₂ ∈ᴮ X),
    by finish,
  apply le_trans this, apply bv_or_elim_left;
    [rw[<-inf_assoc], ac_change' (U =ᴮ u₂ ⊓ u₂ ∈ᴮ X) ⊓ u₁ ∈ᴮ X ≤ U ∈ᴮ X];
    apply inf_le_left_of_le; rw[bv_eq_symm]; apply subst_congr_mem_left
end

lemma two_term_mixture_subset_top (H : a₁ = u₂ ⊆ᴮ u₁) :
  ⊤ ≤ u₂ ⊆ᴮ (two_term_mixture a₁ a₂ h_anti u₁ u₂) :=
begin
  let U := _, change _ ≤ u₂ ⊆ᴮ U,
  rw[subset_unfold'], bv_intro w, apply bv_imp_intro,
  rw[top_inf_eq], simp only [mem_unfold], apply bv_Or_elim,
  intro i, fapply bv_use, exact ⟨ulift.up tt,i⟩, refine inf_le_inf _ (by refl),
  simp, rw[sup_inf_left_right_eq], repeat{apply bv_and_intro},
  {rw[h_partition], apply le_top},
  {apply le_sup_right_of_le, cases u₂, apply mem.mk},
  {have : a₂ = - a₁, by apply eq_neg_of_partition; assumption,
   conv {to_rhs, congr, skip, rw[this, H]}, rw[sup_comm], change _ ≤ _ ⟹ _,
   apply bv_imp_intro, rw[inf_comm], simp only [subset_unfold],
   apply bv_specialize_left i, apply bv_imp_elim},
  {apply le_sup_right_of_le, cases u₂, apply mem.mk}
end
end mixing_corollaries

lemma core_aux_lemma (ϕ : bSet 𝔹 → 𝔹) (h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y) (h_definite : (⨆(w : bSet 𝔹), ϕ w) = ⊤) (v : bSet 𝔹) :
  ∃ u : bSet 𝔹, ϕ u = ⊤ ∧ ϕ v = u =ᴮ v :=
begin
  have := maximum_principle ϕ h_congr, cases this with w H_w,
  let b := ϕ v, let u := two_term_mixture b (- b) (by simp) v w, use u,
  have h_partition : b ⊔ (- b) = ⊤, by simp,
  have H_max : ϕ u = ⊤,
    by {apply top_unique, rw[<-h_partition], apply le_trans,
    apply sup_le_sup, apply le_inf, apply (mixing_lemma_two_term _ _ _ _ _).left, exact -b, simp,
    exact v, exact w, refl, apply le_inf, apply (mixing_lemma_two_term _ _ _ _ _).right, exact b,
    simp, exact v, exact w, swap, exact ϕ w, rw[<-H_w, h_definite], apply le_top,
    apply bv_or_elim; rw[bv_eq_symm]; apply h_congr},
  refine ⟨H_max, _⟩,
  apply le_antisymm,
    {apply (mixing_lemma_two_term _ _ _ _ _).left},
    {suffices : u =ᴮ v ⊓ ϕ u ≤ ϕ v,
      by {rw[H_max] at this, finish}, by apply h_congr}
end

lemma core_aux_lemma2 (ϕ ψ : bSet 𝔹 → 𝔹) (h_congrϕ : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y)
  (h_congrψ : ∀ x y, x =ᴮ y ⊓ ψ x ≤ ψ y) (h_sub : ∀ u, ϕ u = ⊤ → ψ u = ⊤)
  (h_definite : (⨆(w : bSet 𝔹), ϕ w) = ⊤) :
  (⨅(x : bSet 𝔹), ϕ x ⟹ ψ x) = ⊤ :=
begin
  simp, intro x, have := core_aux_lemma ϕ h_congrϕ h_definite x,
  rcases this with ⟨u, ⟨h₁, h₂⟩⟩,
  have := h_sub u ‹_›, rw[show ϕ x = ϕ x ⊓ ⊤, by simp],
  rw[<-this, h₂], apply h_congrψ
end

section smallness'
variables {α : Type u} (ϕ : bSet 𝔹 → α)
-- in this section we prove the smallness-type arguments required for showing that cores always exist.
@[reducible, simp]noncomputable def fiber_lift' (b : ϕ '' set.univ) : {x : bSet 𝔹 // ϕ x = b.val} :=
classical.indefinite_description (λ a : bSet 𝔹, ϕ a = b.val) $
  by {cases b.property, use w, exact h.right}

end smallness'

section cores
@[reducible]def pullback_eq_rel {α β : Type*} (f : α → β) (E : β → β → Prop) : α → α → Prop :=
λ a₁ a₂, E (f a₁) (f a₂)

def core {α : Type u} (u : bSet 𝔹) (S : α → bSet 𝔹) : Prop :=
(∀ x : α, S x ∈ᴮ u = ⊤) ∧ (∀ y : bSet 𝔹, y ∈ᴮ u = ⊤ → ∃! x_y : α, y =ᴮ S x_y = ⊤)

noncomputable def core_witness {α : Type u} {u : bSet 𝔹} {S : α → bSet 𝔹} (h_core : core u S) (x : bSet 𝔹) (h_X : x ∈ᴮ u = ⊤) :
  Σ' (x_y : α), x =ᴮ S x_y = ⊤ :=
begin
  cases h_core, specialize h_core_right x h_X, have := classical.indefinite_description _ h_core_right, use this.val, tidy
end

lemma core_inj {α : Type u} (u : bSet 𝔹) (S : α → bSet 𝔹) (h_core : core u S) : function.injective S :=
begin
  intros x y H, cases h_core, have h_left₁ := h_core_left x, have h_left₂ := h_core_left y,
  have this_right₁ := h_core_right (S x) h_left₁,
  have this_right₂:= h_core_right (S y) h_left₂,
  rcases this_right₁ with ⟨w₁, ⟨H₁, H₂⟩⟩, rcases this_right₂ with ⟨w₂, ⟨H₁', H₂'⟩⟩,
  have Q₂ := H₂ y, have Q₃ := H₂ x (by apply bv_eq_refl), dsimp at *, rw[Q₂], swap, simpa[H]
end

/-- `core_inj` says that if a b : α satisfy S a =ᴮ S b = ⊤, then a = b -/
lemma core_inj' {α : Type u} {u : bSet 𝔹} {S : α → bSet 𝔹} (h_core : core u S) : ∀ a b : α, S a =ᴮ S b = ⊤ → a = b :=
begin
  intros x y H, cases h_core, have h_left₁ := h_core_left x, have h_left₂ := h_core_left y,
  have this_right₁ := h_core_right (S x) h_left₁,
  have this_right₂:= h_core_right (S y) h_left₂,
  rcases this_right₁ with ⟨w₁, ⟨H₁, H₂⟩⟩, rcases this_right₂ with ⟨w₂, ⟨H₁', H₂'⟩⟩,
  have Q₂ := H₂ y H, have Q₂ := H₂ x (by apply bv_eq_refl), cc
end

/-- This is the "f_x" in the notes. We are free to use function types since universes are inaccessible. -/
def core.mk_ϕ (u : bSet 𝔹) : bSet 𝔹 → (u.type → 𝔹) :=
λ x, (λ a, (u.bval a) ⊓ x =ᴮ u.func a )

lemma core.mk_ϕ_inj (u : bSet 𝔹) (x y : bSet 𝔹) : (x ∈ᴮ u = ⊤) → (y ∈ᴮ u = ⊤) → core.mk_ϕ u x = core.mk_ϕ u y → x =ᴮ y = ⊤ :=
begin
  intros h₁ h₂ H, unfold core.mk_ϕ at H, replace H := congr_fun H,
  apply top_unique,
  have : ∀ i_z : u.type, u.bval i_z ⊓ x =ᴮ u.func i_z ⊓ u.bval i_z ⊓ u.func i_z =ᴮ y  ≤ x =ᴮ y :=
    λ i_z, by {tidy_context, from bv_trans (‹_› : Γ ≤ x =ᴮ func u i_z) ‹_›},
    dsimp at H, simp[H] at this, rw[<-supr_le_iff] at this, rw[eq_top_iff] at h₂,
    refine le_trans _ this, convert h₂, rw[mem_unfold], congr' 1, ext,
    refine le_antisymm _ _; tidy_context, from ⟨⟨⟨‹_›,‹_›⟩,‹_›⟩, bv_context_symm ‹_›⟩
end

noncomputable def core.S' (u : bSet 𝔹) : (core.mk_ϕ u '' set.univ) → bSet 𝔹 :=
  λ x, (fiber_lift' (core.mk_ϕ u) x).val

def core.α_S'' (u : bSet 𝔹) : Type u := {i : core.mk_ϕ u '' set.univ // core.S' u i ∈ᴮ u = ⊤}

noncomputable def core.S'' (u : bSet 𝔹) : core.α_S'' u → bSet 𝔹 := λ x, core.S' u x.val

lemma core.S'_spec (u : bSet 𝔹) (x : core.mk_ϕ u '' set.univ) : core.mk_ϕ u (core.S' u x) = x.val :=
 by unfold core.S'; simp[(fiber_lift' (core.mk_ϕ u) x).property]

def core.bv_eq_top : bSet 𝔹 → bSet 𝔹 → Prop :=
  λ x₁ x₂, x₁ =ᴮ x₂ = ⊤

def core.bv_eq_top_setoid : setoid $ bSet 𝔹 :=
{ r := core.bv_eq_top,
  iseqv :=
begin
  repeat{split},
  {apply bv_eq_refl},
  {dsimp[core.bv_eq_top], tidy, rwa[bv_eq_symm]},
  {dsimp[core.bv_eq_top], tidy, apply top_unique, rw[show ⊤ = x =ᴮ y ⊓ y =ᴮ z, by finish],
   apply bv_eq_trans}
end}

instance core.S''_setoid (u : bSet 𝔹) : setoid $ core.α_S'' u :=
{ r := pullback_eq_rel (core.S'' u) core.bv_eq_top,
  iseqv :=
begin
  repeat{split}, intro x, apply bv_eq_refl,
  intros x y, intro H, unfold pullback_eq_rel core.bv_eq_top, rwa[bv_eq_symm],
  intros x y z, unfold pullback_eq_rel core.bv_eq_top, intros H₁ H₂, apply top_unique,
  rw[show ⊤ = (core.S'' u x) =ᴮ (core.S'' u y) ⊓ (core.S'' u y) =ᴮ (core.S'' u z), by finish],
  apply bv_eq_trans
end}

noncomputable def core.mk_aux (u : bSet 𝔹) : (quotient (@core.S''_setoid 𝔹 _ u)) → bSet 𝔹 :=
  λ x, (core.S'' u) (@quotient.out _ (core.S''_setoid u ) x)

@[reducible]private def image.mk {α β : Type*} {f : α → β} (a : α) : f '' set.univ :=
  ⟨f a, by tidy⟩

lemma core.mk (u : bSet 𝔹) : ∃ α : Type u, ∃ S : α → bSet 𝔹, core u S :=
begin
  repeat{split}, show _ → bSet 𝔹, exact core.mk_aux u,
  {dsimp, intro x,unfold core.mk_aux, let y := _, change core.S'' u y ∈ᴮ u = _, apply y.property},
  {intros y H_y, let y' := (core.S' u (image.mk y)),
   have H_y' : core.mk_ϕ u y = core.mk_ϕ u y',
     by rw[core.S'_spec],
   have H_y'2 : y' ∈ᴮ u = ⊤,
     by {unfold core.mk_ϕ at H_y', have := congr_fun H_y',
         simp only [mem_unfold], apply top_unique,
         conv {to_rhs, congr, rw[<-H_y']},
         simpa[mem_unfold] using H_y},

   let y'' := (core.mk_aux u ⟦by split; exact H_y'2⟧),
   have H_y'' : y'' =ᴮ y' = ⊤,
     by {dsimp[y''], unfold core.mk_aux, have := quotient.mk_out,
      show setoid _, exact core.S''_setoid u, apply this},
   have H₃ : y =ᴮ y' = ⊤,
     by {apply core.mk_ϕ_inj, repeat{assumption}},
   have H₁ : y =ᴮ y'' = ⊤,
     by {apply top_unique, apply le_trans, show 𝔹, from y =ᴮ y' ⊓ y' =ᴮ y'',
           apply le_inf,
             {rw[<-eq_top_iff], exact H₃},
             {rw[<-eq_top_iff], convert H_y'' using 1, apply bv_eq_symm},
         apply bv_eq_trans},
   split, refine ⟨H₁, _⟩, intros i H_y''',
   suffices : core.mk_aux u i =ᴮ y' = ⊤,
     by {have : core.mk_aux u i =ᴮ y'' = ⊤, by {apply top_unique, rw[eq_top_iff] at *,
         apply bv_trans this, convert H_y'' using 1, apply bv_eq_symm},
         dsimp[y''] at this, unfold core.mk_aux at this_1,
         have : ⟦quotient.out i⟧ = ⟦quotient.out ⟦⟨image.mk y, H_y'2⟩⟧⟧,
           by {apply quotient.sound, exact this_1},
         convert this using 1; rw[quotient.out_eq]},
   apply top_unique, rw[bv_eq_symm] at H_y''',
     rw[show ⊤ = (core.mk_aux u i =ᴮ y ⊓ y =ᴮ y'), by {dsimp at H_y''', rw [H₃, H_y'''], simp}],
   apply bv_eq_trans}
end
/-- Given a subset C of α, and an α-indexed core S, return the bSet whose underlying type is C,
    such that A is the canonical inclusion and B is always ⊤. -/
def bSet_of_core_set {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} (h : core u S) (C : set α) : bSet 𝔹 :=
⟨C, λ x, S x, λ x, ⊤⟩

def bSet_of_core {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} (h : core u S) : bSet 𝔹 :=
  bSet_of_core_set h set.univ

@[simp]lemma of_core_type {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} {h : core u S} {C : set α} :
  (bSet_of_core_set h C).type = C := rfl
@[simp]lemma of_core_bval {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} {h : core u S} {C : set α} {i} :
  (bSet_of_core_set h C).bval i = ⊤ := rfl

lemma of_core_mem {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} {h : core u S} {C : set α} {i} :
  ⊤ ≤ (bSet_of_core_set h C).func i ∈ᴮ u :=
top_le_iff.mpr (h.left _)

/-- Given a core S for u, pull back the ordering -/
def subset' {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} (h : core u S) : α → α → Prop :=
  λ a₁ a₂, S a₁ ⊆ᴮ S a₂ = ⊤

open classical zorn

def subset'_partial_order {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} (h : core u S) : partial_order α :=
{ le := subset' h,
  lt := λ a₁ a₂, (subset' h a₁ a₂) ∧ a₁ ≠ a₂,
  le_refl := by {simp[subset']},
  le_trans := by {intros a b c, simp only [subset'], intros, rw[eq_top_iff] at a_1 a_2 ⊢,
                   from subset_trans' ‹_› ‹_›},
  lt_iff_le_not_le :=
    begin
      /- `tidy` says -/ intros a b, cases h, dsimp at *, fsplit,
      work_on_goal 0 { intros a_1, cases a_1, fsplit,
        work_on_goal 0 { assumption }, intros a_1 },
      work_on_goal 1 { intros a_1, cases a_1, fsplit,
        work_on_goal 0 { assumption }, intros a_1, induction a_1, solve_by_elim },
      dsimp[subset'] at *,
      suffices : S a = S b,
        by {have := core_inj u _ ⟨h_left, h_right⟩ this, contradiction},
      suffices : a = b, by rw[this]; refl, apply core_inj' ⟨h_left, h_right⟩, dsimp,
      rw[eq_top_iff] at a_1_left a_1 ⊢, from subset_ext ‹_› ‹_›
    end,
  le_antisymm :=
    begin
      intros a b H₁ H₂, apply core_inj' h, unfold subset' at H₁ H₂, rw[eq_top_iff] at H₁ H₂ ⊢,
      from subset_ext ‹_› ‹_›
    end}

local attribute [instance] subset'_partial_order

lemma subset'_trans {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} {h : core u S} : by haveI := subset'_partial_order h; from ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c :=
  by apply partial_order.le_trans

lemma subset'_unfold {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} {h : core u S} {a₁ a₂ : α} :
  by {haveI := subset'_partial_order h, from a₁ ≤ a₂ → (S a₁ ⊆ᴮ S a₂ = ⊤)} := by tidy

lemma exists_mem_of_nonempty (u : bSet 𝔹) {Γ : 𝔹} {H : Γ ≤ -(u =ᴮ ∅)} : Γ ≤ ⨆x, x∈ᴮ u :=
by {apply le_trans H, simp[eq_empty], intro x, apply bv_use (u.func x), apply mem.mk'}

lemma nonempty_of_exists_mem (u : bSet 𝔹) {Γ : 𝔹} {H : Γ ≤ (⨆x, x ∈ᴮ u)} : Γ ≤ -(u =ᴮ ∅) :=
begin
  {apply le_trans H, simp[eq_empty], intro x, rw[mem_unfold], apply bv_Or_elim, intro i, apply bv_use i, apply inf_le_left}
end

lemma core_aux_lemma3 (u : bSet 𝔹) (h_nonempty : -(u =ᴮ ∅) = ⊤) {α : Type u} (S : α → bSet 𝔹) (h_core : core u S) : ∀ x, ∃ y ∈ S '' set.univ, x =ᴮ y = x ∈ᴮ u :=
begin
  intro x, have := core_aux_lemma (λ z, z∈ᴮu) (by intros; apply subst_congr_mem_left)
    (by {apply top_unique, apply exists_mem_of_nonempty, simpa}) x,
    rcases this with ⟨y, ⟨H₁, H₂⟩⟩, cases h_core with H_left H_right,
    specialize H_right y H₁, cases H_right with y' H_y',
    use S y', specialize H_left y', split, use y', finish,
    dsimp at H₁ H₂, rw[H₂], cases H_y', have := bv_rw H_y'_left (λ z, x =ᴮ z),
    simpa[bv_eq_symm] using this, intros x₁ y₁, dsimp, rw[inf_comm], exact bv_eq_trans
end

lemma core_mem_of_mem_image {u y} {α : Type u} {S : α → bSet 𝔹} (h_core : core u S) :
  y ∈ S '' set.univ → y ∈ᴮ u = ⊤ := by tidy

end cores

section check_names
/- `check` is the canonical embedding of pSet into bSet.
note that a check-name is not only definite, but recursively definite
-/
@[simp]def check : (pSet : Type (u+1)) → bSet 𝔹
| ⟨α,A⟩ := ⟨α, λ a, check (A a), λ a, ⊤⟩

postfix `̌ `:90 := check

@[simp, cleanup]lemma check_type {α : Type u} {A : α → pSet} :
  bSet.type ((pSet.mk α A)̌  : bSet 𝔹) = α := rfl

@[simp, cleanup]lemma check_type_infi {α : Type u} {A : α → pSet} {s : α → 𝔹} :
  (⨅(a : bSet.type ((pSet.mk α A)̌  : bSet 𝔹)), s a) = (⨅(a : α), s a : 𝔹) :=
by refl

@[simp, cleanup]lemma check_type_supr {α : Type u} {A : α → pSet} {s : α → 𝔹} :
(⨆(a : bSet.type ((pSet.mk α A)̌   : bSet 𝔹)), s a) = (⨆(a : α), s a : 𝔹) := rfl

@[simp, cleanup]lemma pSet.type_mk {α : Type u} {A : α → pSet} : pSet.type (pSet.mk α A) = α
:= rfl

@[simp, cleanup]lemma check_type' {x : pSet.{u}} : bSet.type (x̌ : bSet 𝔹) = x.type :=
by {induction x, simp}

@[simp, cleanup]lemma check_type'_set {x : pSet} : set (bSet.type (x̌ : bSet 𝔹)) = set (x.type) :=
by {induction x, simp}

@[reducible, simp]def check_cast {x : pSet} (i : (x̌ : bSet 𝔹).type) : x.type :=
cast check_type' i

@[reducible, simp] def check_cast_set {x : pSet} (S : set (x̌ : bSet 𝔹).type) : set (x.type) :=
cast check_type'_set S

lemma check_func {x : pSet} {i} :
  (x̌ : bSet 𝔹).func i = (x.func (check_cast i))̌  :=
by induction x; refl

lemma check_unfold {x : pSet.{u}} : (x̌ : bSet 𝔹) = bSet.mk x.type (λ i, (x.func i)̌ ) (λ i, ⊤) :=
by induction x; refl

@[simp]lemma check_bval_top (x : pSet) {i} : (x̌ : bSet 𝔹).bval i = ⊤ := by induction x; refl

@[simp]lemma check_bval_mk {α : Type u} {A : α → pSet} {i} : ((pSet.mk α A)̌ ).bval i = (⊤ : 𝔹) := rfl

@[simp]lemma check_empty_eq_empty : (∅ : pSet)̌ = (∅ : bSet 𝔹) :=
by {change mk _ _ _ = mk _ _ _, congr, tidy}

 -- this is essentially a restatement of mem.mk/mem.mk', but will be useful later
@[simp]lemma mem_top_of_bval_top {u : bSet 𝔹} {i : u.type} {H_top : u.bval i = ⊤} : u.func i ∈ᴮ u = ⊤ :=
by {apply top_unique, rw[<-H_top], apply mem.mk'}

@[simp]lemma check_mem_top {x : pSet} {i : (x̌ : bSet 𝔹).type} : (x̌).func i ∈ᴮ x̌ = ⊤ :=
by simp

lemma check_bv_eq_top_of_equiv {x y : pSet} :
  pSet.equiv x y → x̌ =ᴮ y̌ = (⊤ : 𝔹) :=
begin
  induction x generalizing y, cases y,
  dsimp[check], simp only [pSet.equiv, lattice.top_le_iff, bSet.check,
  lattice.top_inf_eq, lattice.imp_top_iff_le, lattice.inf_eq_top_iff, lattice.infi_eq_top],
  intros a, cases a, split; intro i;
  apply top_unique; [rcases a_left i with ⟨w, h⟩, rcases a_right i with ⟨w,h⟩];
  apply le_supr_of_le w; simp only [lattice.top_le_iff, bSet.check]; apply (x_ih _); exact h
end

lemma check_bv_eq {x y : pSet} {Γ : 𝔹}  (H : pSet.equiv x y) :
    (Γ : 𝔹) ≤ x̌ =ᴮ y̌ :=
le_trans (le_top) $ by {simp only [top_le_iff], apply check_bv_eq_top_of_equiv ‹_›}

lemma check_bv_eq_bot_of_not_equiv {x y : pSet} :
  (¬ pSet.equiv x y) → (x̌ =ᴮ y̌) = (⊥ : 𝔹) :=
begin
  induction x generalizing y, cases y, dsimp[check], intro H, apply bot_unique,
  cases pSet.not_equiv H with H H; cases H with w H_w;
  [apply inf_le_left_of_le, apply inf_le_right_of_le]; apply infi_le_of_le (w); simp[-le_bot_iff];
  intro a'; rw[le_bot_iff]; apply x_ih; apply H_w
end

lemma check_bv_eq_dichotomy (x y : pSet) :
  (x̌ =ᴮ y̌ = (⊤ : 𝔹)) ∨ (x̌ =ᴮ y̌ = (⊥ : 𝔹)) :=
begin
  haveI : decidable (pSet.equiv x y) := by apply classical.prop_decidable,
  by_cases pSet.equiv x y; [left, right];
  [apply check_bv_eq_top_of_equiv, apply check_bv_eq_bot_of_not_equiv]; assumption
end

lemma check_bv_eq_iff {x y : pSet}
: pSet.equiv x y ↔ x̌ =ᴮ y̌ = (⊤ : 𝔹) :=
begin
  induction x generalizing y, cases y,
  dsimp[check], simp only [pSet.equiv, lattice.top_le_iff, bSet.check,
    lattice.top_inf_eq, lattice.imp_top_iff_le, lattice.inf_eq_top_iff, lattice.infi_eq_top],
  fsplit,
  work_on_goal 0 { intros a, cases a, fsplit, work_on_goal 0 { intros i },
  work_on_goal 1 { intros i } }, work_on_goal 2 { intros a, cases a, fsplit,
  work_on_goal 0 { intros a}}, work_on_goal 3 {intros b},
  {apply top_unique, rcases a_left i with ⟨w, h⟩,  apply le_supr_of_le w,
   simp only [lattice.top_le_iff, bSet.check], apply (x_ih _).mp, exact h},
  {apply top_unique, rcases a_right i with ⟨w, h⟩,  apply le_supr_of_le w,
   simp only [lattice.top_le_iff, bSet.check], apply (x_ih _).mp, exact h},
   all_goals{have := supr_eq_top_max, cases this with w h, use w, apply (x_ih _).mpr, apply h,
   exact nontrivial.bot_lt_top}, apply a_left, work_on_goal 1 {apply a_right},
   all_goals{intros a' H, have := check_bv_eq_dichotomy (x_A ‹x_α›) (y_A ‹y_α›), tidy}
end

lemma not_check_bv_eq_iff {x y : pSet} : ¬ pSet.equiv x y ↔ x̌ =ᴮ y̌ = (⊥ : 𝔹) :=
begin
  refine ⟨_,_⟩; intro H,
    { exact check_bv_eq_bot_of_not_equiv ‹_› },
    { intro H_equiv, have := check_bv_eq_top_of_equiv ‹_›,
      suffices this : ⊥ < (⊥ : 𝔹), by exact lt_irrefl' this,
      rw[this] at H, conv{to_rhs, rw[<-H]}, simp }
end

lemma check_bv_eq_nonzero_iff_eq_top {x y : pSet} : (⊥ : 𝔹) < x̌ =ᴮ y̌  ↔ x̌ =ᴮ y̌ = (⊤ : 𝔹) :=
begin
  refine ⟨_,_⟩; intro H,
    { by_contra, finish[or.resolve_left (check_bv_eq_dichotomy x y) ‹_›] },
    { simp* }
end

@[simp]lemma check_insert (a b : pSet) : (pSet.insert a b)̌  = (bSet.insert1 (ǎ) (b̌) : bSet 𝔹) :=
by {induction a, induction b, simp[pSet.insert, bSet.insert1], split; ext; cases x; simp}

lemma mem_check_witness {y x : pSet.{u}} {Γ : 𝔹} {h_nonzero : ⊥ < Γ} (H : Γ ≤ y̌ ∈ᴮ (x̌)) : ∃ i : x.type, Γ ≤ y̌ =ᴮ (x.func i)̌  :=
begin
  rw[mem_unfold] at H, simp at H,
  have := supr_eq_Gamma_max _ _ _, cases this with w h,
  use w, tactic.rotate 3, from λ a, (y̌ : bSet 𝔹) =ᴮ (x.func a)̌, from Γ,
  from ‹_›, cases x, from H, swap, from ‹_›,
  intros a H, by_contra,
  cases (@check_bv_eq_dichotomy 𝔹 _ y (pSet.func x a)),
    { finish },
    { contradiction }    
end

lemma check_mem_iff {x y : pSet} : x ∈ y ↔ x̌ ∈ᴮ y̌ = (⊤ : 𝔹) :=
begin
  refine ⟨_,_⟩; intro H,
    { cases y, unfold has_mem.mem pSet.mem at H,
      cases H with b Hb, rw[<-top_le_iff], apply bv_use b,
      refine le_inf (by refl) (by rwa[top_le_iff, <-check_bv_eq_iff]) },
    { cases y, rw[<-top_le_iff] at H, replace H := mem_check_witness H, swap, by simp,
      cases H with b Hb, exact ⟨b, by rwa[top_le_iff, <-check_bv_eq_iff] at Hb⟩}
end

lemma not_check_mem_iff {x y : pSet} : x ∉ y ↔ x̌ ∈ᴮ y̌ = (⊥ : 𝔹) :=
begin
  refine ⟨_,_⟩; intro H,
    { rw[<-le_bot_iff, mem_unfold], rw[supr_le_iff],
      intro i, tidy_context, cases y, unfold has_mem.mem pSet.mem at H, push_neg at H,
      have := check_bv_eq_bot_of_not_equiv (H i), convert a_right, exact this.symm },
    { intro this, replace this := check_mem_iff.mp this,
      suffices this : ⊥ < (⊥ : 𝔹), by exact lt_irrefl' this,
      rw[this] at H, conv{to_rhs, rw[<-H]}, simp }
end

lemma check_mem_dichotomy (x y : pSet) : (x̌ ∈ᴮ y̌ = (⊤ : 𝔹)) ∨ (x̌ ∈ᴮ y̌ = (⊥ : 𝔹)) :=
begin
  haveI := classical.prop_decidable, by_cases (x ∈ y);
  {[smt] eblast_using [check_mem_iff, not_check_mem_iff]}
end

lemma check_mem_nonzero_iff_eq_top {x y : pSet} : (⊥ : 𝔹) < x̌ ∈ᴮ y̌  ↔ x̌ ∈ᴮ y̌ = (⊤ : 𝔹) :=
begin
  refine ⟨_,_⟩; intro H,
    { by_contra, finish[or.resolve_left (check_mem_dichotomy x y) ‹_›] },
    { simp* }
end


-- note(jesse): this lemma is not true; one also requires that x is a check-name
-- lemma definite_mem_definite_iff_of_subset_check {x y : bSet 𝔹} (H_definite₁ : is_definite x) (H_definite₂ : is_definite y) (H_sub : ∃ z : pSet, ⊤ ≤ y ⊆ᴮ ž)  : ⊤ ≤ x ∈ᴮ y ↔ ∃ j : y.type, ⊤ ≤ x =ᴮ y.func j :=
-- begin
--   refine ⟨_,_⟩; intro H,
--     { rw[mem_unfold] at H, haveI := classical.prop_decidable, by_contra H', push_neg at H',
--       simp only [lt_top_iff_not_top_le.symm] at H',
--       suffices this : (⨆ (i : type y), bval y i ⊓ x =ᴮ func y i) ≤ ⊥,
--         by {rw[le_bot_iff] at this, rw[this] at H, convert H, simp, },
--       replace H := (by refl : (⨆ (i : type y), bval y i ⊓ x =ᴮ func y i) ≤ ⨆ (i : type y), bval y i ⊓ x =ᴮ func y i),
--       bv_cases_at H j, specialize H' j,
--       suffices this : x =ᴮ func y j ≤ ⊥,
--         by {transitivity bval y j ⊓ x =ᴮ func y j, from ‹_›, rw[le_bot_iff] at this, simp[this]},
--       sorry
--     },
--     { cases H with j Hj, rw[mem_unfold], apply bv_use j, exact le_inf (by {unfold is_definite at H_definite₂, simp* }) (Hj) }
-- end

-- lemma instantiate_existential_over_check
-- {ϕ : bSet 𝔹 → 𝔹} (H_congr : B_ext ϕ) (x : pSet) {Γ} (H_nonzero : ⊥ < Γ) (H_ex : Γ ≤ ⨆y, (y ∈ᴮ (x̌) ⊓ ϕ (y))) :
--   ∃ (Γ' : 𝔹) (H_nonzero : ⊥ < Γ') (H : Γ' ≤ Γ) (z) (H_mem : z ∈ x), Γ' ≤ ϕ (ž) :=
-- begin
--   rw[<-@bounded_exists] at H_ex, swap, by change B_ext _; simpa,
--   cases (nonzero_inf_of_nonzero_le_supr H_nonzero H_ex) with i Hi,
--   refine ⟨_, Hi, _, _, _, _⟩,
--     { tidy_context },
--     { exact (x.func (cast (by cases x; refl) i)) },
--     { convert pSet.mem.mk _ _, simp, },
--     { tidy_context, cases x, exact a_right_right }
-- end

lemma instantiate_existential_over_check_aux {ϕ : bSet 𝔹 → 𝔹} (H_congr : B_ext ϕ) (x : pSet) {Γ} (H_nonzero : ⊥ < Γ) (H_ex : Γ ≤ ⨆y, (y ∈ᴮ (x̌) ⊓ ϕ (y))) : ∃ i : x.type, ⊥ < (ϕ ((x.func i)̌ ) ⊓ Γ) :=
begin
  simp only [inf_comm],
  rw[<-@bounded_exists] at H_ex, swap, by change B_ext _; simpa,
  cases (nonzero_inf_of_nonzero_le_supr H_nonzero H_ex) with i Hi,
  refine ⟨cast check_type' i,_⟩, dsimp at Hi, rw[check_bval_top _, top_inf_eq] at Hi,
  cases x, exact Hi
end

noncomputable def instantiate_existential_over_check
{ϕ : bSet 𝔹 → 𝔹} (H_congr : B_ext ϕ) (x : pSet) {Γ} (H_nonzero : ⊥ < Γ) (H_ex : Γ ≤ ⨆y, (y ∈ᴮ (x̌) ⊓ ϕ (y))) : x.type :=
begin
  apply @classical.some _ (λ i : x.type, ⊥ < ϕ ((x.func i)̌ ) ⊓ Γ),
  apply instantiate_existential_over_check_aux; from ‹_›
end

lemma instantiate_existential_over_check_spec {ϕ : bSet 𝔹 → 𝔹} (H_congr : B_ext ϕ) (x : pSet) {Γ} (H_nonzero : ⊥ < Γ) (H_ex : Γ ≤ ⨆y, (y ∈ᴮ (x̌) ⊓ ϕ (y))) :
 ⊥ < (ϕ ((x.func $ instantiate_existential_over_check ‹_› x ‹_› ‹_›)̌ ) ⊓ Γ) :=
   by {unfold instantiate_existential_over_check, exact classical.some_spec (instantiate_existential_over_check_aux H_congr x H_nonzero ‹_›)}

lemma instantiate_existential_over_check_spec₂ (ϕ : bSet 𝔹 → 𝔹) (H_congr : B_ext ϕ) (x : pSet) {Γ} (H_nonzero : ⊥ < Γ) (H_ex : Γ ≤ ⨆y, (y ∈ᴮ (x̌) ⊓ ϕ (y))) :
  ⊥ < (ϕ ((x.func $ instantiate_existential_over_check ‹_› x ‹_› ‹_›)̌ )) :=
bot_lt_resolve_right H_nonzero (instantiate_existential_over_check_spec ‹_› x ‹_› ‹_›)

/--
  This corresponds to Property 4 in Moore's The method of forcing
-/
lemma eq_check_of_mem_check {Γ : 𝔹} (h_nonzero : ⊥ < Γ) (x : pSet.{u}) (y : bSet 𝔹) (H_mem : Γ ≤ y ∈ᴮ x̌) :
  ∃ i : x.type, ⊥ < y =ᴮ (x.func i)̌  :=
  -- ∃ Γ' (H_le : Γ' ≤ Γ) (z) (H_mem : z ∈ x), (Γ' ≤ y =ᴮ ž) :=
begin
  refine ⟨_,_⟩,
    { refine instantiate_existential_over_check _ x ‹_› _,
      exact λ z, y =ᴮ z, simp, apply bv_use y, exact le_inf ‹_› bv_refl },
    { apply instantiate_existential_over_check_spec₂ }
end

end check_names

/-- The axiom of collection says that for every ϕ(x,y),
    for every set u, ∀ x ∈ u, ∃ y ϕ (x,y) implies there exists a set v
    which contains the image of u under ϕ. With the other axioms,
    this should be equivalent to the usual axiom of replacement. -/
theorem bSet_axiom_of_collection (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹)
  (h_congr_right : ∀ x y z, x =ᴮ y ⊓ ϕ z x ≤ ϕ z y)
  (h_congr_left : ∀ x y z, x =ᴮ y ⊓ ϕ x z ≤ ϕ y z) (u : bSet 𝔹) :
  (⨅(i:u.type), (u.bval i ⟹ (⨆(y : bSet 𝔹), ϕ (u.func i) y))) ⟹
  (⨆(v : bSet 𝔹), (⨅(i : u.type), u.bval i ⟹ (⨆(j:v.type), (v.bval j) ⊓ ϕ (u.func i) (v.func j)))) = ⊤ :=
begin
  simp only [bSet.bval, lattice.imp_top_iff_le, bSet.func, bSet.type],
  rcases (classical.axiom_of_choice (AE_convert u.func u.bval ϕ h_congr_right)) with ⟨wit, wit_property⟩, dsimp at wit wit_property,
  fapply le_supr_of_le, exact ⟨u.type, wit, λ _, ⊤⟩,
    {simp, intro i, apply le_trans (wit_property i),
     apply imp_le_of_right_le, exact le_supr (λ x, ϕ (func u i) (wit x)) i}
end

/-- Same statement, global quantifiers -/
theorem bSet_axiom_of_collection' (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹)
  (h_congr_right : ∀ x y z, x =ᴮ y ⊓ ϕ z x ≤ ϕ z y)
  (h_congr_left : ∀ x y z, x =ᴮ y ⊓ ϕ x z ≤ ϕ y z)
  (u : bSet 𝔹) :
⊤ ≤ ⨅u, ((⨅x, x ∈ᴮ u ⟹ ⨆y, ϕ x y) ⟹ (⨆v, ⨅w, w ∈ᴮ u ⟹ (⨆w', w' ∈ᴮ v ⊓ ϕ w w'))) :=
begin
  bv_intro u, bv_imp_intro,
  have := bSet_axiom_of_collection ϕ ‹_› ‹_› u,
  rw[eq_top_iff] at this, specialize_context_at this Γ,
  replace this := this _,
  bv_cases_at this v, apply bv_use v,
  bv_intro w, bv_imp_intro, rename H_1 H_w,
  rw[mem_unfold] at H_w, bv_cases_at H_w i,
  bv_split, replace this_1 := this_1 i ‹_›,
  bv_cases_at this_1 j, apply bv_use (func v j), bv_split,
  apply le_inf, from mem.mk'' ‹_›, apply bv_rw' H_w_1_right,
  unfold B_ext, intros x y, apply h_congr_left x y,
  from ‹_›, bv_intro i, bv_imp_intro, rename H_1 H_i,
  from H (u.func i) (mem.mk'' ‹_›)
end

/-- The boolean-valued unionset operator -/
def bv_union (u : bSet 𝔹) : bSet 𝔹 :=
  ⟨Σ(i : u.type), (u.func i).type, λ x, (u.func x.1).func x.2,
       λ x, ⨆(y : u.type), u.bval y ⊓ (u.func x.1).func x.2 ∈ᴮ (u.func y)⟩

lemma func_cast {u x : bSet 𝔹} {i_y : u.type} {α : Type u} {A : α → bSet 𝔹} {B : α → 𝔹} {h : func u i_y = mk α A B} {i_x' : α} : func (func u i_y) (eq.mpr (by rw[h]; refl) i_x') = A i_x' :=
begin
  change _ = (mk α A B).func i_x',
  have : func (mk α A B) (eq.mpr rfl i_x') = func (mk α A B) i_x', by refl,
  convert this
end

lemma bv_union_spec (u : bSet 𝔹) : ⊤ ≤ ⨅ (x : bSet 𝔹), (x ∈ᴮ bv_union u ⟹ ⨆ (y : type u), u.bval y ⊓ x ∈ᴮ func u y) ⊓
        ((⨆ (y : type u), u.bval y ⊓ x ∈ᴮ func u y) ⟹ x ∈ᴮ bv_union u) :=
begin
  bv_intro x, apply le_inf,
    {simp only [bv_union, lattice.top_le_iff, lattice.imp_top_iff_le,
     sigma.forall, lattice.supr_le_iff], intros a i, apply bv_cases_left,
     intro a', apply bv_use a', simp only [inf_assoc],
    apply inf_le_inf, refl, rw[inf_comm,bv_eq_symm], apply B_ext_mem_left},
    {simp only [lattice.top_le_iff, bSet.bval, bSet.mem, mem_unfold,
               lattice.imp_top_iff_le, bSet.func, bSet.type, lattice.supr_le_iff, bv_union],
     intro i, dsimp, apply bv_cases_right, intro i_1, fapply bv_use, use i, from i_1,
     apply le_inf,
       {apply bv_use i, apply inf_le_inf, refl, apply bv_use i_1,
       apply inf_le_inf, apply refl, simp[bv_eq_refl]},
       {rw[<-inf_assoc], apply inf_le_right_of_le, refl}},
end

lemma bv_union_spec' (u : bSet 𝔹) {Γ} : Γ ≤ ⨅ (x : bSet 𝔹), (x ∈ᴮ bv_union u ⟹ ⨆ y, y ∈ᴮ u ⊓ x ∈ᴮ y) ⊓
        ((⨆ y, y ∈ᴮ u ⊓ x ∈ᴮ y) ⟹ x ∈ᴮ bv_union u) :=
begin
  have := bv_union_spec u,
  bv_intro x, apply le_inf,
    replace this := this x, bv_split_at this,
    from le_trans (le_top) (by {bv_imp_intro, replace this_1 := this_1 ‹_›,
    bv_cases_at this_1 i_y, apply bv_use (u.func i_y), bv_split,
    from le_inf (mem.mk'' ‹_›) ‹_›}),
  replace this := this x, bv_split_at this,
  bv_imp_intro, specialize_context_at this_1_1 Γ_1,
  replace this_1_1 := this_1_1 _, from ‹_›,
  rw[@bounded_exists 𝔹 _ u (λ z, x ∈ᴮ z)], from ‹_›,
  change B_ext _, simp
end

lemma bv_union_spec_split (u : bSet 𝔹) {Γ} (x : bSet 𝔹) : (Γ ≤ x ∈ᴮ bv_union u) ↔ (Γ ≤ ⨆ y, y ∈ᴮ u ⊓ x ∈ᴮ y) :=
begin
  have := bv_union_spec' u, show 𝔹, from Γ, replace this := this x,
  dsimp at this, bv_split_at this, split; intro, from this_1 ‹_›,
  from this_1_1 ‹_›
end

/-- For every x ∈ u, x ⊆ᴮ ⋃ u.-/
lemma bv_union_spec'' (u : bSet 𝔹) : ⊤ ≤ ⨅(x : bSet 𝔹), (x ∈ᴮ u) ⟹ (x ⊆ᴮ bv_union u) :=
begin
  bv_intro x, rw[<-deduction], simp[subset_unfold], intro i_v, rw[<-deduction, inf_comm],
  apply le_trans, apply inf_le_inf, apply mem.mk', refl,
  have := bv_union_spec u,
  apply bv_have, apply le_trans, apply le_top, exact this,
  apply bv_specialize_right (x.func i_v), rw[inf_comm],
  ac_change' (func x i_v ∈ᴮ bv_union u ⟹ ⨆ (y : type u), u.bval y ⊓ func x i_v ∈ᴮ func u y) ⊓
        (((⨆ (y : type u), u.bval y ⊓ func x i_v ∈ᴮ func u y) ⟹ func x i_v ∈ᴮ bv_union u) ⊓
      (func x i_v ∈ᴮ x ⊓ x ∈ᴮ u)) ≤
    func x i_v ∈ᴮ bv_union u, apply inf_le_right_of_le,
    suffices : (func x i_v ∈ᴮ x ⊓ x ∈ᴮ u) ≤ (⨆ (y : type u), bval u y ⊓ func x i_v ∈ᴮ func u y),
      by {apply le_trans, apply inf_le_inf, refl, exact this, apply bv_imp_elim},
    conv in (x ∈ᴮ u) {simp only [mem_unfold]}, apply bv_cases_right, intro y,
    apply bv_use y,
    ac_change' bval u y ⊓ (func x i_v ∈ᴮ x ⊓ x =ᴮ func u y) ≤ u.bval y ⊓ (func x i_v ∈ᴮ func u y),
    apply inf_le_inf, refl, rw[inf_comm], apply subst_congr_mem_right
end

lemma bv_union_congr {x y : bSet 𝔹} {Γ} (H_eq : Γ ≤ x =ᴮ y) : Γ ≤ bv_union x =ᴮ bv_union y :=
begin
  apply mem_ext; bv_intro z; bv_imp_intro,
    have := bv_union_spec x z, bv_split,
    specialize_context_at this_left Γ_1,
    specialize_context_at this_right Γ_1,
    replace this_left := this_left H,
    have := bv_union_spec y z, bv_split,
    specialize_context_at this_left_1 Γ_1,
    specialize_context_at this_right_1 Γ_1,
    replace this_right_1 := this_right_1 _, from ‹_›,
    rw[@bounded_exists 𝔹 _ y (λ w, z ∈ᴮ w)],
    rw[@bounded_exists 𝔹 _ x (λ w, z ∈ᴮ w)] at this_left,
    bv_cases_at this_left w, bv_split_at this_left_2,
    apply bv_use w, apply le_inf,
    apply bv_rw' (bv_symm H_eq), simp, from ‹_›,
    from ‹_›, change B_ext _, simp, change B_ext _, simp,

    have := bv_union_spec y z, bv_split,
    specialize_context_at this_left Γ_1,
    specialize_context_at this_right Γ_1,
    replace this_left := this_left H,
    have := bv_union_spec x z, bv_split,
    specialize_context_at this_left_1 Γ_1,
    specialize_context_at this_right_1 Γ_1,
    replace this_right_1 := this_right_1 _, from ‹_›,
    rw[@bounded_exists 𝔹 _ x (λ w, z ∈ᴮ w)],
    rw[@bounded_exists 𝔹 _ y (λ w, z ∈ᴮ w)] at this_left,
    bv_cases_at this_left w, bv_split_at this_left_2,
    apply bv_use w, apply le_inf,
    apply bv_rw' (H_eq), simp, from ‹_›,
    from ‹_›, change B_ext _, simp, change B_ext _, simp
end

theorem bSet_axiom_of_union : (⨅ (u : bSet 𝔹), (⨆v, ⨅x,
  (x ∈ᴮ v ⇔ (⨆(y : u.type), u.bval y ⊓ x ∈ᴮ u.func y)))) = ⊤ :=
begin
  simp only [bSet.mem, lattice.biimp, bSet.func, lattice.infi_eq_top, bSet.type],intro u,
  apply top_unique, apply bv_use (bv_union u), exact @bv_union_spec 𝔹 _ u
end

@[reducible, simp]def set_of_indicator {u : bSet 𝔹} (f : u.type → 𝔹) : bSet 𝔹 :=
  ⟨u.type, u.func, f⟩

@[simp, cleanup]lemma set_of_indicator.type {u} {f} :
  (@set_of_indicator 𝔹 _ u f).type = u.type := rfl

@[simp, cleanup]lemma set_of_indicator.func {u} {f} {i}:
  (@set_of_indicator 𝔹 _ u f).func i = u.func i := rfl

@[simp, cleanup]lemma set_of_indicator.bval {u} {f} {i} :
  (@set_of_indicator 𝔹 _ u f).bval i = f i := rfl

@[reducible, simp]def set_of_indicator' {u : bSet 𝔹} (f : u.type → 𝔹) : bSet 𝔹 :=
  ⟨u.type, u.func, λ i, f i ⊓ u.bval i⟩

def bv_powerset (u : bSet 𝔹) : bSet 𝔹 :=
⟨u.type → 𝔹, λ f, set_of_indicator f, λ f, set_of_indicator f ⊆ᴮ u⟩

prefix `𝒫`:80 := bv_powerset

def bv_powerset' (u : bSet 𝔹) : bSet 𝔹 :=
⟨u.type → 𝔹, λ f, set_of_indicator' f, λ f, ⊤⟩

--TODO (jesse) try proving bv_powerset and bv_powerset' are equivalent

-- example {u : bSet 𝔹} : bv_powerset u =ᴮ bv_powerset' u = ⊤ :=
-- begin
--   apply top_unique, apply le_trans, swap, apply bSet_axiom_of_extensionality,
--   bv_intro z, apply le_inf; apply bv_imp_intro; simp[top_inf_eq],
--   {unfold bv_powerset, dsimp, apply supr_le, intro f,
--   unfold bv_powerset', simp, apply le_supr_of_le f,
--    refine le_trans _ (by apply bSet_axiom_of_extensionality),
--    bv_intro z',
--    have := @bounded_forall _ _ (set_of_indicator f) (λ x, x ∈ᴮ u), dsimp[set_of_indicator] at this, simp[subset_unfold], rw[this],
--    rw[deduction], apply infi_le_of_le z', rw[supr_imp_eq],
--    apply bv_imp_intro, apply le_inf, apply bv_imp_intro,
--    ac_change'  (⨅ (i : type u), f i ⊓ z' =ᴮ func u i ⟹ z' ∈ᴮ u) ⊓ (z =ᴮ mk (type u) (func u) f ⊓ z' ∈ᴮ z) ≤ z' ∈ᴮ mk (type u) (func u) (λ (i : type u), f i ⊓ bval u i),
--    apply le_trans, apply inf_le_inf, refl, apply subst_congr_mem_right,
--    rw[inf_comm], rw[deduction], apply supr_le, intro i',
--    rw[<-deduction], apply le_supr_of_le i', dsimp,
--    repeat{apply le_inf}, apply inf_le_left_of_le, apply inf_le_left_of_le, refl,
--    repeat{sorry}

-- },
--   {sorry}
-- end



lemma bSet_axiom_of_powerset' {Γ : 𝔹} (u : bSet 𝔹) : Γ ≤ ⨅(x : bSet 𝔹), x∈ᴮ 𝒫 u ⇔ ⨅(y : x.type), x.bval y ⟹ (x.func y ∈ᴮ u) :=
begin
  bv_intro x, apply le_inf,
  {apply le_trans le_top,
   rw[<-deduction, top_inf_eq],
   unfold bv_powerset, apply supr_le, intro χ,
   suffices : ((set_of_indicator χ) ⊆ᴮ u ⊓ (x =ᴮ (set_of_indicator χ)) : 𝔹) ≤ x ⊆ᴮ u,
     by {convert this, simp[subset_unfold]},
   apply subst_congr_subset_left},
  {apply le_trans le_top,
    have := @bounded_forall _ _ x (λ y, (y ∈ᴮ u))
      (by {intros x y, apply subst_congr_mem_left}), rw[this],
  dsimp,
  unfold bv_powerset, simp[subset_unfold], fapply le_supr_of_le,
  from λ i, u.func i ∈ᴮ x,
  have this' := @bounded_forall _ _ (set_of_indicator (λ y, (u.func y ∈ᴮ x))) (λ y, (y ∈ᴮ u))
    (by {intros x y, apply subst_congr_mem_left}), dsimp at this', rw[this'],
  apply le_inf, bv_intro a', apply infi_le_of_le a', rw[supr_imp_eq],
  bv_intro i_y, apply imp_le_of_left_right_le, swap, refl,
  rw[inf_comm, bv_eq_symm], apply subst_congr_mem_left,

  rw[bv_eq_unfold], apply le_inf,
  {conv {to_rhs, dsimp}, have := @bounded_forall _ _ x (λ y, ⨆ (a' :    type u), func u a' ∈ᴮ x ⊓ y =ᴮ func u a'), rw[this], swap,
  intros a₁ a₂, dsimp, rw[inf_supr_eq], apply supr_le, intro i,

  apply le_supr_of_le i,
  ac_change' (a₂ =ᴮ a₁ ⊓  a₁ =ᴮ func u i) ⊓ func u i ∈ᴮ x ≤ func u i ∈ᴮ x ⊓ a₂ =ᴮ func u i,
    rw[bv_eq_symm], ac_refl,

  apply le_trans, apply inf_le_inf, apply bv_eq_trans, refl, rw[inf_comm],

  {bv_intro a₁, dsimp, apply infi_le_of_le a₁, rw[<-deduction],
   apply le_trans, apply bv_imp_elim', rw[inf_comm, deduction],
   rw[mem_unfold], apply supr_le, intro i, rw[<-deduction],
   apply le_supr_of_le i,
   apply le_inf, rw[inf_assoc], apply inf_le_right_of_le,
   apply subst_congr_mem_left,
   ac_change' a₁ =ᴮ func u i ⊓ (bval u i ⊓ a₁ ∈ᴮ x) ≤ a₁ =ᴮ func u i,
   apply inf_le_left_of_le, refl}},

   {have := @bounded_forall _ _ (set_of_indicator (λ y, func _ y ∈ᴮ x)) (λ y, y ∈ᴮ x),
   rw[this], swap, simp[subst_congr_mem_left],
   bv_intro a₁, apply infi_le_of_le a₁,
   unfold set_of_indicator, dsimp, rw[supr_imp_eq],
   bv_intro i, apply from_empty_context,
   rw[inf_comm, bv_eq_symm], simp[-bv_eq_symm,subst_congr_mem_left]}}
end

theorem bSet_axiom_of_powerset : (⨅(u : bSet 𝔹), ⨆(v : _), ⨅(x : bSet 𝔹), x∈ᴮ v ⇔ ⨅(y : x.type), x.bval y ⟹ (x.func y ∈ᴮ u)) = ⊤:=
begin
  apply top_unique, bv_intro u, apply bv_use (𝒫 u),
  apply bSet_axiom_of_powerset'
end

lemma bv_powerset_spec {u x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ x ⊆ᴮ u ↔ Γ ≤ x ∈ᴮ 𝒫 u :=
begin
  have := bSet_axiom_of_powerset' u, show 𝔹, from Γ,
  simp only [lattice.biimp] at this,
  replace this := this x, bv_split, rw[subset_unfold],
  fsplit; intro H; [from this_right ‹_›, from this_left ‹_›]
end

lemma bv_powerset_congr {Γ : 𝔹} {x y : bSet 𝔹} : Γ ≤ x =ᴮ y → Γ ≤ 𝒫 x =ᴮ 𝒫 y :=
begin
  intro H, apply mem_ext; bv_intro z; bv_imp_intro,
  rw[<-bv_powerset_spec], apply bv_rw' (bv_symm H), simp,
  rwa[bv_powerset_spec], rw[<-bv_powerset_spec],
  apply bv_rw' H, simp, rwa[bv_powerset_spec]
end

lemma set_of_indicator_mem.mk {x : bSet 𝔹} {i : x.type} {χ : x.type → 𝔹} {Γ} (H_Γ : Γ ≤ χ i) : Γ ≤ (x.func i) ∈ᴮ (set_of_indicator χ) :=
by {rw[mem_unfold], apply bv_use i, exact le_inf H_Γ (bv_refl)}

lemma set_of_indicator_subset {x : bSet 𝔹} {χ : x.type → 𝔹} {Γ} (H_χ : ∀ i, χ i ≤ x.bval i) : Γ ≤ set_of_indicator χ ⊆ᴮ x :=
begin
  rw[subset_unfold], bv_intro j, bv_imp_intro H,
  simpa using le_trans (le_trans H (by solve_by_elim)) (mem.mk' _ _)
end

lemma check_set_of_indicator_subset {x : pSet} {χ : x̌.type → 𝔹} {Γ} : Γ ≤ set_of_indicator χ ⊆ᴮ x̌ :=
set_of_indicator_subset (by simp)

/--
 For x an injective pSet and χ : x̌.type → 𝔹, ⊤ ≤ (x.func i) ∈ set_of_indicator χ iff χ i = ⊤.
-/
lemma check_mem_set_of_indicator_iff {x : pSet} (H_inj : ∀ i₁ i₂ : x.type, pSet.equiv (x.func i₁) (x.func i₂) → i₁ = i₂) (i : x.type) {χ : x̌.type → 𝔹} : (∀{Γ}, Γ ≤ (x.func i)̌  ∈ᴮ set_of_indicator χ) ↔ (∀ {Γ}, Γ ≤ χ (cast check_type'.symm i)) :=
begin
  refine ⟨_,_⟩; intro H,
    { intro Γ, have H' := @H Γ, bv_cases_at H' j, bv_split,

      haveI := classical.prop_decidable, by_cases i = (cast check_type' j),
        { subst h, convert H'_1_left, cases x, refl },
        { replace H_inj := mt (H_inj i (cast check_type' j)) ‹_›,
          have := check_bv_eq_bot_of_not_equiv ‹_›,
          transitivity ⊥,
            { rw[<-this], convert H'_1_right, cases x, refl },
            { exact bot_le }}},
    { intro Γ, specialize @H Γ, apply bv_use (cast check_type'.symm i),
      cases x, exact le_inf ‹_› bv_refl }
end

lemma subset_of_pointwise_bounded {Γ : 𝔹} {x : bSet 𝔹} {p : x.type → 𝔹} {p' : x.type → 𝔹} (H_bd : ∀ i : x.type, p i ≤ p' i) : Γ ≤ set_of_indicator p ⊆ᴮ set_of_indicator p' :=
begin
  simp[subset_unfold], intro i, bv_imp_intro, apply bv_use i,
  from le_inf (le_trans H (by simp*)) bv_refl
end

lemma pointwise_bounded_of_check_subset_check {x : pSet} {p₁ p₂ : x̌.type → 𝔹} (H_inj : ∀ i₁ i₂ : x.type, pSet.equiv (x.func i₁) (x.func i₂) → i₁ = i₂)(H_eq : ∀ {Γ}, Γ ≤ (set_of_indicator p₁ ⊆ᴮ set_of_indicator p₂)) : ∀ i, p₁ i ≤ p₂ i :=
begin
  intro i, have : (p₁ i) ≤ (set_of_indicator p₁ ⊆ᴮ set_of_indicator p₂) := H_eq,
  unfold set_of_indicator at this, rw[subset_unfold] at this,
  replace this := this i (by refl), refine le_trans this _,
  simp, intro j, haveI := classical.prop_decidable, by_cases i = j,
    { subst h, simp },
    { specialize H_inj (cast check_type' i) (cast check_type' j),
      replace H_inj := mt H_inj,
      suffices this : ¬pSet.equiv (pSet.func x (cast check_type' i)) (pSet.func x (cast check_type' j)),
        by {refine inf_le_right_of_le _, convert bot_le,
            convert check_bv_eq_bot_of_not_equiv ‹_›; cases x; simp; refl},
      exact (H_inj (by cases x; from ‹_›))}
end

lemma pointwise_eq_of_eq_set_of_indicator {x : pSet} {p₁ p₂ : x̌.type → 𝔹} (H_inj : ∀ i₁ i₂ : x.type, pSet.equiv (x.func i₁) (x.func i₂) → i₁ = i₂) (H_eq : ∀ {Γ}, Γ ≤ (set_of_indicator p₁ =ᴮ set_of_indicator p₂)) : ∀ i, p₁ i = p₂ i :=
begin
  rw[eq_iff_subset_subset] at H_eq, refine (λ i, le_antisymm _ _);
    { apply pointwise_bounded_of_check_subset_check, from ‹_›,
      intro Γ, specialize @H_eq Γ, bv_split, from ‹_› }
end

lemma set_of_indicator_eq_iff_pointwise_eq {x : pSet} {p₁ p₂ : x̌.type → 𝔹} (H_inj : ∀ i₁ i₂ : x.type, pSet.equiv (x.func i₁) (x.func i₂) → i₁ = i₂) :
(∀ {Γ}, Γ ≤ (set_of_indicator p₁ =ᴮ set_of_indicator p₂)) ↔ (∀i, p₁ i = p₂ i)  :=
begin
  refine ⟨_,_⟩,
    { intro H_eq, apply pointwise_eq_of_eq_set_of_indicator; from ‹_› },
    { intros H_eq Γ, rw[show p₁ = p₂, from funext H_eq], simp }
end

section infinity
local notation `ω` := pSet.omega

@[simp]lemma check_omega_type : (ω̌ : bSet 𝔹).type = ulift ℕ := rfl
@[simp]lemma check_omega_func : (ω̌: bSet 𝔹).func = λ x, check (pSet.of_nat x.down) := rfl

postfix `̃ `:70 := pSet.of_nat -- i'm a bit skeptical of this notation

@[simp, reducible]def axiom_of_infinity_spec (u : bSet 𝔹) : 𝔹 :=
  (∅∈ᴮ u) ⊓ (⨅(i_x : u.type), ⨆(i_y : u.type), (u.func i_x ∈ᴮ u.func i_y))

@[reducible]def contains_empty (u : bSet 𝔹) : 𝔹 := ∅ ∈ᴮ u

@[reducible]def contains_succ (u : bSet 𝔹) : 𝔹 := (⨅(i_x : u.type), ⨆(i_y : u.type), (u.func i_x ∈ᴮ u.func i_y))

lemma infinity_of_empty_succ {u : bSet 𝔹} {c} (h₁ : c ≤ contains_empty u)
  (h₂ : c ≤ contains_succ u) : c ≤ axiom_of_infinity_spec u :=
le_inf ‹_› ‹_›

lemma contains_empty_check_omega : (⊤ : 𝔹) ≤ contains_empty (ω̌) :=
by {dsimp[pSet.omega,check, contains_empty], apply bv_use (ulift.up nat.zero), simp[pSet.of_nat]}

lemma contains_succ_check_omega : (⊤ : 𝔹) ≤ contains_succ (ω̌) :=
begin
  bv_intro n, induction n, apply bv_use (ulift.up (n + 1)),
  simp only [lattice.top_le_iff, bSet.check_omega_func, bSet.check,
  bSet.mem, bSet.func, bSet.type], induction n; simp[pSet.of_nat, *]
end

theorem bSet_axiom_of_infinity : (⨆(u : bSet 𝔹), axiom_of_infinity_spec u) = ⊤ :=
begin
  apply top_unique, apply bv_use (ω̌), apply infinity_of_empty_succ,
  exacts [contains_empty_check_omega, contains_succ_check_omega]
end

@[reducible]def omega := (ω̌ : bSet 𝔹)

@[simp, cleanup]lemma omega_type : (omega : bSet 𝔹).type = ulift ℕ := rfl

/-- The n-th von Neumann ordinal in bSet 𝔹 is just the check-name of the n-th von Neumann ordinal in pSet -/
@[reducible]def of_nat : ℕ → bSet 𝔹 := λ n, (pSet.of_nat n)̌

@[simp, cleanup]lemma omega_func {k} : (omega : bSet 𝔹).func k = of_nat k.down :=
by refl

lemma omega_definite {n : ℕ} {Γ : 𝔹} : Γ ≤ of_nat n ∈ᴮ omega :=
begin
suffices : of_nat n ∈ᴮ omega = (⊤ : 𝔹), from le_trans le_top (by rwa[top_le_iff]),
  induction n, {apply top_unique, apply bv_use (ulift.up 0), simp},
  {apply top_unique, apply bv_use (ulift.up (n_n + 1)), simp}
end

instance has_zero_bSet : has_zero (bSet 𝔹) := ⟨of_nat 0⟩

instance has_one_bSet : has_one (bSet 𝔹) := ⟨of_nat 1⟩

example : 0 ∈ᴮ 1 = (⊤ : 𝔹) :=
by {apply top_unique, unfold has_zero.zero, apply bv_use none, simp}

@[simp, cleanup]lemma omega_bval {k} : (omega : bSet 𝔹).bval k = ⊤ :=
by refl

theorem bSet_axiom_of_infinity' :
  (⊤ : 𝔹) ≤ (∅ ∈ᴮ omega) ⊓ (⨅x, x ∈ᴮ omega ⟹ ⨆y, y ∈ᴮ omega ⊓ x ∈ᴮ y) :=
begin
  apply le_inf, apply contains_empty_check_omega,
  rw [←bounded_forall],
  rw [infi_congr], swap,
  intro n, rw [←bounded_exists, omega_bval, top_imp,
                @supr_congr _ _ _ (λ m, func omega n ∈ᴮ func omega m)],
  intro m, rw [omega_bval, top_inf_eq],
  { intros, apply subst_congr_mem_right },
  { exact contains_succ_check_omega },
  { change B_ext _, simp }
end

end infinity

theorem bSet_epsilon_induction (ϕ : bSet 𝔹 → 𝔹) (h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y) :
  (⨅(x : bSet 𝔹), ((⨅(y : bSet 𝔹), y ∈ᴮ x ⟹ ϕ y) ⟹ ϕ x)) ⟹ (⨅(z : bSet 𝔹), ϕ z) = ⊤ :=
begin
  apply top_unique, apply bv_imp_intro, rw[top_inf_eq],
  bv_intro x, let b := _, change b ≤ _,
  induction x with α A B ih, dsimp at *,
  have : b ≤ ⨅(i_y:α), B i_y ⟹ ϕ (A i_y),
    by {bv_intro i_y, specialize ih i_y, apply le_trans ih,
    rw[<-deduction], apply inf_le_left},
  have h := @bounded_forall _ _ (mk α A B) ϕ h_congr,
  simp only with cleanup at h, rw[h] at this,
  apply bv_have this,
  have : b ≤ (⨅ (y : bSet 𝔹), (y) ∈ᴮ (mk α A B) ⟹ ϕ (y)) ⟹ ϕ (mk α A B),
    by {apply bv_specialize (mk α A B), refl},
  rw[deduction], apply le_trans this, rw[<-deduction], apply bv_imp_elim
end

-- the natural induction principle for bSet 𝔹 will always suffice where regularity/epsilon_induction are required
lemma epsilon_induction {Γ} (ϕ : bSet 𝔹 → 𝔹) (h_congr : B_ext ϕ) (H_ih : ∀ x, Γ ≤ ((⨅(y : bSet 𝔹), y ∈ᴮ x ⟹ ϕ y) ⟹ ϕ x)) :
∀ z, Γ ≤ ϕ z  :=
begin
  have := bSet_epsilon_induction ϕ h_congr, rw[eq_top_iff] at this,
  intro z,
  have H_a : Γ ≤ (⨅ (x : bSet 𝔹), (⨅ (y : bSet 𝔹), y ∈ᴮ x ⟹ ϕ y) ⟹ ϕ x),
  bv_intro x, specialize H_ih x, from ‹_›,
  have := le_trans (le_top) this,
  bv_imp_elim_at this H_a, bv_specialize_at H z, exact H_1
end

@[elab_as_eliminator]protected lemma rec_on' {C : bSet 𝔹 → Sort*} (y : bSet 𝔹) : (Π(x : bSet 𝔹), (Π(a : x.type), C (x.func a)) → C x) → C y :=
by {induction y, intro IH, apply IH, from λ a, y_ih a ‹_›}

@[elab_as_eliminator]protected lemma rec' {C : bSet 𝔹 → Sort*} : (Π(x : bSet 𝔹), (Π(a : x.type), C (x.func a)) → C x) → Π(y : bSet 𝔹), C y :=
by {intro H, intro y, induction y with α A B, solve_by_elim}

lemma regularity_aux (x : bSet 𝔹) {Γ : 𝔹} : Γ ≤ ⨅u, x ∈ᴮ u ⟹ ⨆y, y ∈ᴮ u ⊓ (⨅z', z' ∈ᴮ u ⟹ (-(z' ∈ᴮ y))) :=
begin
  apply bSet.rec_on' x, clear x, intros x IH,
    bv_intro u, bv_imp_intro,
    have := bv_em Γ_1 (⨅z', z' ∈ᴮ u ⟹ (-(z' ∈ᴮ x))),
    bv_or_elim_at this, apply bv_use x, from le_inf ‹_› ‹_›,
    rw[neg_infi] at H_right, bv_cases_at H_right x_a,
    rw[neg_imp] at H_right_1, bv_split,
    rw[lattice.neg_neg] at H_right_1_right,
    rw[mem_unfold] at H_right_1_right, bv_cases_at H_right_1_right a,
    bv_split, have H_in : Γ_4 ≤ (func x a) ∈ᴮ u,
    rw[bv_eq_symm] at H_right_1_right_1_right,
    apply @bv_rw' 𝔹 _ _ _ _  H_right_1_right_1_right (λ z, z ∈ᴮ u), simp, from ‹_›,
    from (le_trans (by {dsimp*, simp[inf_le_right_of_le]} : Γ_4 ≤ Γ) (IH a u)) ‹_›
end

theorem bSet_axiom_of_regularity (x : bSet 𝔹) {Γ : 𝔹} (H : Γ ≤ -(x =ᴮ ∅)) : Γ ≤ ⨆y, y∈ᴮ x ⊓ (⨅z', z' ∈ᴮ x ⟹ (- (z' ∈ᴮ y))) :=
begin
  have H_u := exists_mem_of_nonempty x, show 𝔹, from Γ, swap, from ‹_›,
  bv_cases_at H_u u, have := (regularity_aux u), show 𝔹, from Γ_1, from this x ‹_›,
end

/-- ∃! x, ϕ x ↔ ∃ x ∀ y, ϕ(x) ⊓ ϕ (y) → y = x -/
@[reducible]def bv_exists_unique (ϕ : bSet 𝔹 → 𝔹) : 𝔹 :=
  ⨆(x:bSet 𝔹), (⨅(y : bSet 𝔹), ϕ y ⟹ (y =ᴮ x))

local notation `⨆!` binders `, ` r:(scoped f, bv_exists_unique f) := r

section zorns_lemma
open classical zorn

lemma B_ext_subset_or_subset_left (y : bSet 𝔹) : B_ext (λ x, x ⊆ᴮ y ⊔ y ⊆ᴮ x) := by simp

lemma B_ext_subset_or_subset_right (x : bSet 𝔹) : B_ext (λ y, x ⊆ᴮ y ⊔ y ⊆ᴮ x) := by simp

lemma forall_forall_reindex (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹) {h₁ : ∀ x, B_ext (λ y, ϕ x y)}
  {h₂ : ∀ y, B_ext (λ x, ϕ x y)} {C : bSet 𝔹} :
  (⨅(i₁:C.type), (C.bval i₁ ⟹ ⨅(i₂ : C.type), C.bval i₂ ⟹ ϕ (C.func i₁) (C.func i₂))) =
  ⨅(w₁ w₂ : bSet 𝔹), w₁∈ᴮ C ⊓ w₂ ∈ᴮ C ⟹ ϕ w₁ w₂ :=
begin
  have := @bounded_forall _ _ C (λ x, ⨅(i₂ : C.type), bval C i₂ ⟹ ϕ x (func C i₂)),
  rw[this], dsimp at *, apply le_antisymm,
  bv_intro w₁, bv_intro w₂, apply bv_specialize w₁, rw[<-deduction],
  simp only [inf_assoc.symm], rw[deduction], apply le_trans, apply bv_imp_elim,
  have := @bounded_forall _ _ C (λ z, ϕ w₁ z), rw[this], apply bv_specialize w₂,
  apply bv_imp_intro, apply le_trans, apply bv_imp_elim, refl,
  intros w₁ w₂, apply h₁, bv_intro w₁, apply infi_le_of_le w₁, apply bv_imp_intro,
  have := @bounded_forall _ _ C (λ z, ϕ w₁ z), rw[this],
  bv_intro w₂, apply bv_specialize_left w₂, apply bv_imp_intro, simp only [inf_assoc],
  apply le_trans, apply bv_imp_elim, refl, intros w₁ w₂, apply h₁,
  intros w₁ w₂, apply B_ext_infi, intro j,
  apply B_ext_imp; simp*
end

lemma subset'_inductive (X : bSet 𝔹) (H : ⊤ ≤ (⨅y, (y ⊆ᴮ X ⊓ (⨅(w₁ : bSet 𝔹), ⨅(w₂ : bSet 𝔹),
  w₁ ∈ᴮ y ⊓ w₂ ∈ᴮ y ⟹ (w₁ ⊆ᴮ w₂ ⊔ w₂ ⊆ᴮ w₁))) ⟹ (bv_union y ∈ᴮ X))) {α : Type*} {S : α → bSet 𝔹} (h_core : core X S) :
   by {haveI := subset'_partial_order h_core, from ∀c:set α, @chain α (≤) c → ∃ub, ∀a∈c, a ≤ ub} :=
begin
  intros C C_chain, let C' := bSet_of_core_set h_core C,
  /- First, we show that C' is internally a chain -/
  have H_internal_chain : ⊤ ≤ ⨅ i₁ : C'.type, C'.bval i₁ ⟹ ⨅ i₂ : C'.type, C'.bval i₂ ⟹ (C'.func i₁ ⊆ᴮ C'.func i₂ ⊔ C'.func i₂ ⊆ᴮ C'.func i₁),
  by {simp[subset_unfold], intros i₁ i₂,
  simp[chain, set.pairwise_on] at C_chain,
  cases i₁ with i₁ H₁, cases i₂ with i₂ H₂,
  specialize C_chain i₁ H₁ i₂ H₂,
  haveI : decidable_eq α := λ _ _, prop_decidable _,
  by_cases i₁ = i₂,
    subst h, apply top_unique, apply le_sup_left_of_le,
      bv_intro j, apply bv_imp_intro, rw[top_inf_eq], apply mem.mk',
    specialize C_chain h, cases C_chain; apply top_unique;
    [apply le_sup_left_of_le, apply le_sup_right_of_le];
    have := subset'_unfold C_chain; rw[eq_top_iff] at this;
    convert this using 1; simp only [subset_unfold]; refl},

  have H_in_X : ⊤ ≤ ⨅(u : C'.type), C'.bval u ⟹ C'.func u ∈ᴮ X,
    by {bv_intro i_u, rw[of_core_bval, top_imp], apply of_core_mem},
    /- Show that ⋃C' is in X -/
  have H_internal_ub_mem : ⊤ ≤ (bv_union C') ∈ᴮ X,
    by {rw[le_infi_iff] at H, specialize H C', apply bv_context_apply H, apply le_inf,

         {apply le_trans H_in_X, simp only [subset_unfold]},

         {apply le_trans H_internal_chain,
          rw[forall_forall_reindex (λ z₁ z₂, ((z₁ ⊆ᴮ z₂) ⊔ (z₂ ⊆ᴮ z₁) : 𝔹))]; simp}},
 /- Show that ⋃C' is an upper bound on C' in X -/
  have H_internal_ub_spec : ⊤ ≤ ⨅(i_w : C'.type), C'.bval i_w ⟹ C'.func i_w ⊆ᴮ (bv_union C'),
    by {have := bv_union_spec'' C', apply le_trans this,
        have := @bounded_forall 𝔹 _ C' (λ w, w ⊆ᴮ bv_union C'), dsimp only at this, rw[this_1],
        intros x y, rw[inf_comm, bv_eq_symm], apply subst_congr_subset_left},

  have := core_witness h_core (bv_union C') (by {rw[eq_top_iff], exact H_internal_ub_mem}),
  cases this with w w_property, use w, intros x_w' H_x_w', change S (x_w') ⊆ᴮ S w = ⊤,
  apply top_unique, apply le_trans H_internal_ub_spec, apply bv_specialize, swap,
  use x_w', from H_x_w', rw[of_core_bval, top_imp],
  fapply bv_have, exact bv_union C' =ᴮ S w, rw[w_property], apply le_top,
  apply subst_congr_subset_right
end


/- ∀ x, x ≠ ∅ ∧ ((∀ y, y ⊆ x ∧ ∀ w₁ w₂ ∈ y, w₁ ⊆ w₂ ∨ w₂ ⊆ w₁) → (⋃y) ∈ x)
      → ∃ c ∈ x, ∀ z ∈ x, c ⊆ x → c = x -/
theorem bSet_zorns_lemma (X : bSet 𝔹) (H_nonempty : -(X =ᴮ ∅) = ⊤) (H : ⊤ ≤ (⨅y, (y ⊆ᴮ X ⊓ (⨅(w₁ : bSet 𝔹), ⨅(w₂ : bSet 𝔹),
  w₁ ∈ᴮ y ⊓ w₂ ∈ᴮ y ⟹ (w₁ ⊆ᴮ w₂ ⊔ w₂ ⊆ᴮ w₁))) ⟹ (bv_union y ∈ᴮ X))) :
  ⊤ ≤ (⨆c, c ∈ᴮ X ⊓ (⨅z, z ∈ᴮ X ⟹ (c ⊆ᴮ z ⟹ c =ᴮ z))) :=
begin
  have := core.mk X, rcases this with ⟨α, ⟨S, h_core⟩⟩,
  have H_zorn := zorn (subset'_inductive X H h_core) (by apply subset'_trans),
  rcases H_zorn with ⟨c, H_c⟩, rcases h_core with ⟨h_core_l, h_core_r⟩,
  have H_c_in_X := h_core_l c, apply bv_use (S c), rw[H_c_in_X],
  rw[top_inf_eq], bv_intro x, apply bv_imp_intro, rw[top_inf_eq],
  have := core_aux_lemma3 X H_nonempty S ⟨h_core_l, h_core_r⟩ x,
  rcases this with ⟨y, ⟨H₁_y, H₂_y⟩⟩, rw[<-H₂_y], apply bv_imp_intro,
  conv in (S c =ᴮ _) {rw[bv_eq_symm]},
  suffices : x =ᴮ y ⊓ (S c ⊆ᴮ y) ≤ x =ᴮ S c,
    by {apply le_trans, show 𝔹, from x =ᴮ y ⊓ S c ⊆ᴮ y,
        apply le_inf, apply inf_le_left, apply B_ext_subset_right, from this},
  suffices : S c ⊆ᴮ y ≤ y =ᴮ S c,
    by {apply le_trans, apply inf_le_inf, refl, from this, apply bv_eq_trans},
  let a := S c ⊆ᴮ y, have h_a_bot : a ⊓ (-a) = ⊥, by apply inf_neg_eq_bot,
  have h_a_top : a ⊔ (-a) = ⊤, by apply sup_neg_eq_top,
  let v := two_term_mixture a (-a) h_a_bot y (S c),
  have claim_1 : v ∈ᴮ X = ⊤,
    by {apply two_term_mixture_mem_top, from h_a_top, apply core_mem_of_mem_image ⟨‹_›,‹_›⟩ ‹_›,
    from ‹_›},
  have claim_2 : Σ' z : α, v =ᴮ S z = ⊤ := core_witness ⟨‹_›,‹_›⟩ v claim_1,
  rcases claim_2 with ⟨z, H_z⟩,
  have claim_3 : ⊤ ≤ S c ⊆ᴮ v,
    by {apply two_term_mixture_subset_top, from ‹_›, refl},
  have claim_4 : by haveI := subset'_partial_order ⟨h_core_l,h_core_r⟩; from c ≤ z,
    by {apply top_unique, apply le_trans' claim_3, rw[<-H_z], apply B_ext_subset_right},
  have claim_5 : S c =ᴮ S z = ⊤,
    by {have : S z ⊆ᴮ S c = ⊤, apply H_c z claim_4,
        apply top_unique, rw[eq_iff_subset_subset], apply le_inf,
        rw[top_le_iff], from ‹_›, rw[<-this]},
  change a ≤ _, apply le_trans, apply (mixing_lemma_two_term a (-a) ‹_› y (S c)).left,
  change v =ᴮ _ ≤ _, rw[bv_eq_symm], apply le_trans', show 𝔹, from v =ᴮ S z, rw[H_z],
  apply le_top, apply le_trans, apply bv_eq_trans, apply bv_have (le_top : y =ᴮ _ ≤ _),
  rw[bv_eq_symm] at claim_5, simp[claim_5.symm, bv_eq_trans]
end
end zorns_lemma

-- /-- This is the abbreviated version of AC found at http://us.metamath.org/mpeuni/ac3.html
--     It is provably equivalent over ZF to the usual formulation of AC
--     After we have the Boolean soundness theorem, we can transport the proof via completeness
--     from the 2-valued setting to the 𝔹-valued setting -/
-- -- ∀x ∃𝑦 ∀𝑧 ∈ 𝑥 (𝑧 ≠ ∅ → ∃!𝑤 ∈ 𝑧 ∃𝑣 ∈ 𝑦 (𝑧 ∈ 𝑣 ∧ 𝑤 ∈ 𝑣))
-- theorem bSet_axiom_of_choice :
-- (⨅(x : bSet 𝔹), ⨆(y : bSet 𝔹), ⨅(z : bSet 𝔹),
--   z ∈ᴮ x ⟹ ((- (z =ᴮ ∅)) ⟹
--   (⨆!(w : bSet 𝔹), w ∈ᴮ z ⟹
--     ⨆(v : bSet 𝔹), v ∈ᴮ y ⟹ (z ∈ᴮ v ⊓ w ∈ᴮ v)))) = ⊤ := sorry

end bSet
