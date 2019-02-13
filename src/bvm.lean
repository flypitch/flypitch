import fol set_theory.zfc order.boolean_algebra order.complete_boolean_algebra .cohen_poset

open lattice

universe u

/- A β-valued model of ZFC -/

namespace lattice
def imp {α : Type*} [boolean_algebra α] : α → α → α :=
  λ a₁ a₂, (- a₁) ⊔ a₂

infix ` ⟹ `:50 := lattice.imp

lemma imp_neg_sub {α : Type*} [boolean_algebra α] {a₁ a₂ : α} :  -(a₁ ⟹ a₂) = a₁ - a₂ :=
  by {rw[sub_eq, imp]; finish}

lemma inf_eq_of_le {α : Type*} [distrib_lattice α] {a b : α} (h : a ≤ b) : a ⊓ b = a :=
  by apply le_antisymm; finish[le_inf]

/-- the deduction theorem in β -/
@[simp]lemma imp_top_iff_le {α : Type*} [boolean_algebra α] {a₁ a₂ : α} : (a₁ ⟹ a₂ = ⊤) ↔ a₁ ≤ a₂ :=
begin
 split; intro H,
  {have : a₁ ⊓ a₂ = a₁, from
    calc a₁ ⊓ a₂ = ⊥ ⊔ (a₁ ⊓ a₂) : by simp
             ... = (a₁ ⊓ - a₁) ⊔ (a₁ ⊓ a₂) : by simp
             ... = a₁ ⊓ (- a₁ ⊔ a₂) : by {rw[inf_sup_left]}
             ... = a₁ ⊓ ⊤ : by {rw[<-H], refl}
             ... = a₁ : by {simp},
             
   finish},
 {have : a₁ ⊓ a₂ = a₁, from inf_eq_of_le H, apply top_unique,
  have this' : ⊤ = - a₁ ⊔ a₁, by rw[lattice.neg_sup_eq_top],
  rw[this', <-this, imp], simp only [lattice.neg_inf, lattice.sup_le_iff],
  repeat{split},
    suffices : (- a₁ ≤ - a₁ ⊔ - a₂ ⊔ a₂) = (- a₁ ≤ - a₁ ⊔ (- a₂ ⊔ a₂)),
      by rw[this]; apply le_sup_left, ac_refl,
    suffices : (-a₂ ≤ -a₁ ⊔ -a₂ ⊔ a₂) = (- a₂ ≤ - a₂ ⊔ (-a₁ ⊔ a₂)),
      by rw[this]; apply le_sup_left, ac_refl,
    suffices : - a₁ ⊔ - a₂ ⊔ a₂ = ⊤,
      by rw[this]; simp, apply top_unique,
      suffices : - a₁ ⊔ - a₂ ⊔ a₂ = - a₁ ⊔ (- a₂ ⊔ a₂),
        by simp[this], ac_refl}
end

/-- Given an η : option α → β, where β is a complete lattice, we have that the supremum of η
    is equal to (η none) ⊔ ⨆(a:α) η (some a)-/
@[simp]lemma supr_option {α β : Type*} [complete_lattice β] {η : option α → β} : (⨆(x : option α), η x) = (η none) ⊔ ⨆(a : α), η (some a) :=
begin
  apply le_antisymm, tidy, cases i, apply le_sup_left,
  apply le_sup_right_of_le, apply le_supr (λ x, η (some x)) i, apply le_supr, apply le_supr
end

/-- Given an η : option α → β, where β is a complete lattice, we have that the infimum of η
    is equal to (η none) ⊓ ⨅(a:α) η (some a)-/
@[simp]lemma infi_option {α β : Type*} [complete_lattice β] {η : option α → β} : (⨅(x : option α), η x) = (η none) ⊓ ⨅(a : α), η (some a) :=
begin
  apply le_antisymm, tidy, tactic.rotate 2, cases i, apply inf_le_left,
  apply inf_le_right_of_le, apply infi_le (λ x, η (some x)) i, apply infi_le, apply infi_le
end

lemma supr_option' {α β : Type*} [complete_lattice β] {η : α → β} {b : β} : (⨆(x : option α), (option.rec b η x : β) : β) = b ⊔ ⨆(a : α), η a :=
  by rw[supr_option]

lemma infi_option' {α β : Type*} [complete_lattice β] {η : α → β} {b : β} : (⨅(x : option α), (option.rec b η x : β) : β) = b ⊓ ⨅(a : α), η a :=
  by rw[infi_option]



end lattice

-- note: use forall_and_distrib in core, which is the same statement but with the ↔ reversed

-- lemma forall_and {α : Type*} {p q : α → Prop} : (∀ x, p x) ∧ (∀ y, q y) ↔ ∀ x, p x ∧ q x :=
--   by finish

-- τ is a B-name if and only if τ is a set of pairs of the form ⟨σ, b⟩, where σ is
-- a B-name and b ∈ B.
inductive bSet (β : Type u) [complete_boolean_algebra β] : Type (u+1)
| mk (α : Type u) (A : α → bSet) (B : α → β) : bSet

namespace bSet
variables {β : Type u} [complete_boolean_algebra β]

/-- The underlying type of a bSet -/
@[simp]def type : bSet β → Type u
| ⟨α, _, _⟩ := α

@[simp]lemma type_infi {α : Type*} {A : α → bSet β} {B C : α → β} : (⨅(a : type (mk α A B)), C a) = ⨅(a : α), C a := by refl

@[simp]lemma type_supr {α : Type*} {A : α → bSet β} {B C : α → β} : (⨆(a : type (mk α A B)), C a) = ⨆(a : α), C a := by refl

/-- The indexing function of a bSet -/
@[simp]def func : ∀ x : bSet β, x.type → bSet β
| ⟨_, A, _⟩ := A

/-- The boolean truth-value function of a bSet -/
@[simp]def bval : ∀ x : bSet β, x.type → β
| ⟨_, _, B⟩ := B

def empty : bSet β :=
  ⟨ulift empty, empty.elim ∘ ulift.down, empty.elim ∘ ulift.down⟩

instance nonempty_bSet : nonempty $ @bSet β _ :=
  ⟨empty⟩

instance has_empty_bSet : has_emptyc (bSet β) := ⟨empty⟩

/-- Two Boolean-valued pre-sets are extensionally equivalent if every
  element of the first family is extensionally equivalent to
  some element of the second family and vice-versa. -/
@[reducible, simp]def bool_equiv : ∀ (x y : bSet β), β
/- ∀ x ∃ y, m x y ∧ ∀ y ∃ x, m y x, but this time in ~lattice~ -/
| ⟨α, A, B⟩ ⟨α', A', B'⟩ :=
             (⨅a : α, B a ⟹ ⨆a', B' a' ⊓ bool_equiv (A a) (A' a')) ⊓
               (⨅a' : α', B' a' ⟹ ⨆a, B a ⊓ bool_equiv (A a) (A' a'))

infix ` =ᴮ `:80 := bool_equiv

theorem bool_equiv_refl_empty : (@bool_equiv β _) (empty) (empty) = ⊤ :=
  by unfold empty bool_equiv;
  {simp only [lattice.inf_eq_top_iff, lattice.infi_eq_top], fsplit; intros i; cases i; cases i}

open lattice

@[simp]theorem bool_equiv_refl : ∀ x, @bool_equiv β _ x x = ⊤ :=
begin
  intro x, induction x, simp[bool_equiv, -imp_top_iff_le], split; intros;
  {apply top_unique, simp, apply le_supr_of_le i, have := x_ih i, finish}
end

/- empty' is the singleton bSet {⟨∅, ⊥⟩}, i.e. a set whose only member is ∅ which has
   a zero probability of actually being an element. It should be equivalent to ∅. -/
@[reducible]def empty' : bSet β := mk punit (λ _, ∅) (λ _, ⊥)

example : empty =ᴮ empty = (⊤ : β) := by simp

/-- `x ∈ y` as Boolean-valued pre-sets if `x` is extensionally equivalent to a member
  of the family `y`. -/
@[reducible, simp]def mem : bSet β → bSet β → β
| a (mk α' A' B') := ⨆a', B' a' ⊓ a =ᴮ A' a'

@[reducible]def empty'' : bSet β :=
  mk (ulift bool) (λ x, ∅) (λ x, by {repeat{cases x}, exact ⊥, exact ⊤})

infix ` ∈ᴮ `:80 := mem

/-- ∅ appears in empty'' with probability 0 and 1, with the higher probability winning the
    vote of membership. This demonstrates why the inequality in the following theorem is
    necessary. -/
example : ∅ ∈ᴮ empty'' = (⊤ : β) :=
  by {apply top_unique, apply le_supr_of_le ⊤, swap, exact ⟨⟨(tt)⟩⟩, finish}

theorem mem.mk {α : Type*} (A : α → bSet β) (B : α → β) (a : α) : A a ∈ᴮ mk α A B ≥ B a :=
  le_supr_of_le a $ by simp

protected def subset : bSet β → bSet β → β
| (mk α A B) b := ⨅a:α, B a ⟹ (A a ∈ᴮ b)

@[simp]protected def insert : bSet β → β → bSet β → bSet β
| u b ⟨α, A, B⟩ := ⟨option α, λo, option.rec u A o, λo, option.rec b B o⟩

protected def insert' : bSet β → β → bSet β → bSet β
| u b ⟨α, A, B⟩ := ⟨unit ⊕ α, λ o, sum.rec (λ_, u) A o, λ o, sum.rec (λ_, b) B o⟩

@[reducible, simp]protected def insert1 : bSet β → bSet β → bSet β
| u v := bSet.insert u ⊤ v

instance insert_bSet : has_insert (bSet β) (bSet β) :=
  ⟨λ u v, bSet.insert1 u v⟩

@[simp]lemma insert_rw {y z : bSet β} : insert y z = bSet.insert y ⊤ z :=     by refl

@[simp]theorem mem_insert {x y z : bSet β} {b : β} : x ∈ᴮ bSet.insert y b z = (b ⊓ x =ᴮ y) ⊔ x ∈ᴮ z :=
  by induction y; induction z; simp

theorem mem_insert1 {x y z : bSet β} : x ∈ᴮ insert y z = x =ᴮ y ⊔ x ∈ᴮ z :=
  by simp

example : {∅} =ᴮ empty'' = (⊤ : β) :=
begin
  simp[empty'', singleton, insert, has_insert.insert], simp[has_emptyc.emptyc, empty], refine ⟨_, by intro i; repeat{cases i}⟩, apply top_unique,
 have : ⊤ = (ulift.rec (bool.rec ⊥ ⊤) : ulift bool → β) (ulift.up tt),
   by refl,
 rw[this], apply le_supr
end

theorem bSet_axiom_of_extensionality (x y : bSet β) :
  x =ᴮ y = (⨅(a : x.type), x.bval a ⟹ (⨆(a' : y.type), y.bval a' ⊓ x.func a =ᴮ y.func a'))
          ⊓ ⨅(a' : y.type), y.bval a' ⟹ (⨆(a : x.type), x.bval a ⊓ x.func a =ᴮ y.func a') :=
  by induction x; induction y; simp

/-- The axiom of weak replacement says that for every ϕ(x,y),
    for every set u, ∀ x ∈ u, ∃ y ϕ (x,y) implies there exists a set v
    which contains the image of u under ϕ. With the other axioms,
    this should be equivalent to the usual axiom of replacement. -/
theorem bSet_axiom_of_weak_replacement (ϕ : bSet β → bSet β → β) (u : bSet β) :
  (⨅(i:u.type), (u.bval i ⟹ (⨆(y : bSet β), ϕ (u.func i) y))) ⟹
  (⨆(v : bSet β), (⨅(i : u.type), u.bval i ⟹ (⨆(j:v.type), ϕ (u.func i) (v.func j)))) = ⊤ :=
begin
  simp, fapply le_supr_of_le; sorry -- todo write the choice application
end

/-- Mixing lemma, c.f. Bell's book or Lemma 1 of Hamkins-Seabold -/

lemma mixing_lemma {A : set β} (h_anti : antichain A) (τ : A → bSet β) :
  ∃ x, ∀ a : β, a ∈ A → a ≤ x =ᴮ τ ⟨a, by assumption⟩ := sorry


end bSet
