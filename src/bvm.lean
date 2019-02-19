import fol set_theory.zfc order.boolean_algebra order.complete_boolean_algebra .cohen_poset tactic.rewrite tactic.monotonicity

open lattice

universe u

/- A β-valued model of ZFC -/

namespace lattice

theorem inf_supr_eq {α ι : Type*} [complete_distrib_lattice α] {a : α} {s : ι → α} :
  a ⊓ (⨆(i:ι), s i) = ⨆(i:ι), a ⊓ s i :=
  eq.trans inf_Sup_eq $
    begin
      rw[<-inf_Sup_eq], suffices : (⨆(i:ι), a ⊓ s i) = ⨆(b∈(set.range s)), a ⊓ b,
      by {rw[this], apply inf_Sup_eq}, simp, apply le_antisymm,
      apply supr_le, intro i, apply le_supr_of_le (s i), apply le_supr_of_le i,
      apply le_supr_of_le rfl, refl,
      repeat{apply supr_le, intro}, rw[<-i_2], apply le_supr_of_le i_1, refl
    end

theorem sup_infi_eq {α ι : Type*} [complete_distrib_lattice α] {a : α} {s : ι → α} :
  a ⊔ (⨅(i:ι), s i) = ⨅(i:ι), a ⊔ s i :=
  eq.trans sup_Inf_eq $
    begin
      rw[<-sup_Inf_eq], suffices : (⨅(i:ι), a ⊔ s i) = ⨅(b∈(set.range s)), a ⊔ b,
      by {rw[this], apply sup_Inf_eq}, simp, apply le_antisymm,
      repeat{apply le_infi, intro}, rw[<-i_2], apply infi_le_of_le i_1, refl,
      repeat{apply infi_le_of_le}, show ι, from ‹ι›, show α, exact s i, refl, refl
    end

@[simp]lemma inf_self {α : Type*} [lattice α] {a : α} : a ⊓ a = a :=
  by finish

@[simp]lemma sup_self {α : Type*} [lattice α] {a : α} : a ⊔ a = a :=
  by finish

def imp {α : Type*} [boolean_algebra α] : α → α → α :=
  λ a₁ a₂, (- a₁) ⊔ a₂

infix ` ⟹ `:50 := lattice.imp

@[simp]lemma imp_le_of_right_le {α : Type*} [boolean_algebra α] {a a₁ a₂ : α} {h : a₁ ≤ a₂} : a ⟹ a₁ ≤ (a ⟹ a₂) :=
  sup_le (by apply le_sup_left) $ le_sup_right_of_le h

@[simp]lemma imp_le_of_left_le {α : Type*} [boolean_algebra α] {a a₁ a₂ : α} {h : a₂ ≤ a₁} : a₁ ⟹ a ≤ (a₂ ⟹ a) :=
  sup_le (le_sup_left_of_le $ neg_le_neg h) (by apply le_sup_right)


lemma imp_neg_sub {α : Type*} [boolean_algebra α] {a₁ a₂ : α} :  -(a₁ ⟹ a₂) = a₁ - a₂ :=
  by rw[sub_eq, imp]; finish

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

/- ∀ {α : Type u_1} [_inst_1 : boolean_algebra α] {a₁ a₂ : α}, a₁ ⟹ a₂ = ⊤ ↔ a₁ ≤ a₂ -/

lemma curry_uncurry {α : Type*} [boolean_algebra α] {a b c : α} : ((a ⊓ b) ⟹ c) = (a ⟹ (b ⟹ c)) :=
  by simp[imp]; ac_refl

/-- the actual deduction theorem in β, thinking of ≤ as a turnstile -/
lemma deduction {α : Type*} [boolean_algebra α] {a b c : α} : a ⊓ b ≤ c ↔ a ≤ (b ⟹ c) :=
  by {[smt] eblast_using [curry_uncurry, imp_top_iff_le]}

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

/-- γ is full with respect to the complete lattice β if for every P : γ → β,
    there exists a y : γ such that ⨆(z : γ), P z ≤ P y -/
class full (γ β : Type*) [complete_lattice β] :=
  (has_supr_wit : ∀ P : γ → β, ∃ y : γ, ((⨆(z : γ), P z) ≤ P y))

lemma full_supr_wit {γ β : Type*} [complete_lattice β] [full γ β] (P : γ → β) : ∃ y : γ, (⨆(z : γ), P z) ≤ P y :=
  by {tactic.unfreeze_local_instances, cases _inst_2, exact has_supr_wit P}

/-- Convert a Boolean-valued ∀∃-statement into a Prop-valued ∀∃-statement
  Given A : α → γ, a binary function ϕ : γ → γ → β, a truth-value assignment
  B : α → β, ∀ i : α, there exists a y_i : γ, such that
  (B i ⟹ ϕ (A i) y_i) ≥ ⨅(i:α), B i ⟹ ⨆(y : γ), ϕ(A i, γ)

  A more verbose, but maybe clearer way to see this is:
  if there is an equality (⨅i-⨆j body i j) = b,
  then for all i, there exists j, such that body i j ≥ b

  Actually, the maximum principle tells us that "≥" above can
  be improved to "="
-/
lemma choice {α β γ : Type*} [complete_boolean_algebra β] [full γ β] (A : α → γ) (B : α → β) (ϕ : γ → γ → β) :
  ∀ i : α, ∃ y : γ, (⨅(j:α), (B j ⟹ ⨆(z : γ), ϕ (A j) z)) ≤ (B i ⟹ ϕ (A i) y) :=
  λ i,
    by {have := classical.indefinite_description _ (full_supr_wit (λ x, ϕ (A i) x)),
      exact ⟨this.val,
    by {fapply infi_le_of_le, exact i, apply imp_le_of_right_le; exact this.property}⟩}

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

noncomputable instance decidable_eq_β : decidable_eq β := λ _ _, classical.prop_decidable _

run_cmd mk_simp_attr `cleanup

/-- The underlying type of a bSet -/
@[simp, cleanup]def type : bSet β → Type u
| ⟨α, _, _⟩ := α

@[simp, cleanup]lemma type_infi {α : Type*} {A : α → bSet β} {B C : α → β} : (⨅(a : type (mk α A B)), C a) = ⨅(a : α), C a := by refl

@[simp, cleanup]lemma type_supr {α : Type*} {A : α → bSet β} {B C : α → β} : (⨆(a : type (mk α A B)), C a) = ⨆(a : α), C a := by refl

/-- The indexing function of a bSet -/
@[simp, cleanup]def func : ∀ x : bSet β, x.type → bSet β
| ⟨_, A, _⟩ := A

/-- The boolean truth-value function of a bSet -/
@[simp, cleanup]def bval : ∀ x : bSet β, x.type → β
| ⟨_, _, B⟩ := B

@[simp, cleanup]def mk_type_func_bval : ∀ x : bSet β, mk x.type x.func x.bval = x :=
  λ x, by induction x; {simp only with cleanup, repeat{split, repeat{refl}}}

def empty : bSet β :=
  ⟨ulift empty, empty.elim ∘ ulift.down, empty.elim ∘ ulift.down⟩

instance nonempty_bSet : nonempty $ @bSet β _ :=
  ⟨empty⟩

instance has_empty_bSet : has_emptyc (bSet β) := ⟨empty⟩

/-- Two Boolean-valued pre-sets are extensionally equivalent if every
element of the first family is extensionally equivalent to
  some element of the second family and vice-versa. -/
@[reducible]def bool_equiv : ∀ (x y : bSet β), β
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

theorem bool_equiv_symm {x y : bSet β} : x =ᴮ y = y =ᴮ x :=
begin
  induction x with α A B generalizing y, induction y with α' A' B',
  suffices : ∀ a : α, ∀ a' : α', A' a' =ᴮ A a = A a =ᴮ A' a',
    by {simp[bool_equiv, this, inf_comm]}, from λ _ _, by simp[x_ih ‹α›]
end

theorem bSet_bool_equiv_rw (x y : bSet β) :
  x =ᴮ y = (⨅(a : x.type), x.bval a ⟹ (x.func a ∈ᴮ y))
          ⊓ (⨅(a' : y.type), (y.bval a' ⟹ (y.func a' ∈ᴮ x))) :=
 by induction x; induction y; simp[mem,bool_equiv,bool_equiv_symm]

theorem bSet_axiom_of_extensionality (x y : bSet β) :
(⨅(z : bSet β), (z ∈ᴮ x ⟹ z ∈ᴮ y) ⊓ (z ∈ᴮ y ⟹ z ∈ᴮ x)) ≤ x =ᴮ y :=
begin
  rw[bSet_bool_equiv_rw],
  apply le_inf; apply le_infi; intro i,
  {fapply infi_le_of_le (x.func i), apply inf_le_left_of_le,
   induction x, unfold mem, simp, by apply imp_le_of_left_le; apply le_supr_of_le i;
   exact le_inf (by refl) (by rw[bool_equiv_refl]; apply le_top)},
  {fapply infi_le_of_le (y.func i), apply inf_le_right_of_le,
   induction y, unfold mem, simp, by apply imp_le_of_left_le; apply le_supr_of_le i;
   exact le_inf (by refl) (by rw[bool_equiv_refl]; apply le_top)},
end

theorem bool_equiv_trans {x y z : bSet β} : (x =ᴮ y ⊓ y =ᴮ z) ≤ x =ᴮ z :=
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
        convert @x_ih a (A' a') (A'' a'') using 1; simp[bool_equiv_symm], ac_refl},
    apply le_inf,
      {apply le_infi, intro i, apply deduction.mp,
        change _ ≤ (A i) ∈ᴮ ⟨α'', A'', B''⟩,
       have this1 : ⟨α, A, B⟩ =ᴮ ⟨α', A', B'⟩ ⊓ B i ≤ A i ∈ᴮ ⟨α', A', B'⟩,
         by {rw[deduction], apply inf_le_left_of_le, apply infi_le},
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
      {apply le_infi, intro i'', apply deduction.mp,
        conv {to_rhs, congr, funext, rw[bool_equiv_symm]}, change _ ≤ (A'' i'') ∈ᴮ ⟨α, A, B⟩,
        have this1 : ⟨α'', A'', B''⟩ =ᴮ ⟨α', A', B'⟩ ⊓ B'' i'' ≤ A'' i'' ∈ᴮ ⟨α', A', B'⟩,
          by {rw[deduction], apply inf_le_left_of_le, apply infi_le},
        suffices : A'' i'' ∈ᴮ ⟨α', A', B'⟩ ⊓ ⟨α', A', B'⟩ =ᴮ ⟨α, A, B⟩ ≤ A'' i'' ∈ᴮ ⟨α, A, B⟩,
         by {have := le_trans (inf_le_inf this1 (by refl)) this,
              convert this using 1, simp[bool_equiv_symm], ac_refl},
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

/-- If u = v and u ∈ w, then this implies that v ∈ w -/
lemma subst_congr_mem_left {u v w : bSet β} : u =ᴮ v ⊓ u ∈ᴮ w ≤ v ∈ᴮ w :=
begin
  cases w,
  have : ∀ a : w_α, u =ᴮ v ⊓ w_B a ⊓ u =ᴮ w_A a ≤ w_B a ⊓ v =ᴮ w_A a,
    by {intro a, have := inf_le_inf (by refl : w_B a ≤ w_B a) (@bool_equiv_trans _ _ v u (w_A a)), convert this using 1, simp[bool_equiv_symm, inf_comm, inf_assoc]},
  convert supr_le_supr this, simp[inf_supr_eq], congr, ext, ac_refl
end

/-- If v = w and u ∈ v, then this implies that u ∈ w -/
lemma subst_congr_mem_right {u v w : bSet β} : (v =ᴮ w ⊓ u ∈ᴮ v) ≤ u ∈ᴮ w :=
begin
  induction v, rw[inf_supr_eq], apply supr_le, intro i,
  suffices : mk v_α ‹_› ‹_› =ᴮ w ⊓ v_B i ≤ v_A i ∈ᴮ w,
  have := le_trans (inf_le_inf this (by refl : u =ᴮ v_A i ≤ u =ᴮ v_A i)) _,
  rw[<-inf_assoc], convert this using 1,
  rw[bool_equiv_symm, inf_comm], apply subst_congr_mem_left,
  rw[deduction], cases w, apply inf_le_left_of_le, apply infi_le
end

def mixture {ι : Type u} (a : ι → β) (u : ι → bSet β) : bSet β :=
  ⟨Σ(i : ι), (u i).type, λx, (u x.fst).func x.snd, λx, ⨆(j:ι), a j ⊓ ((u x.fst).func x.snd) ∈ᴮ u j⟩

@[simp]lemma bval_mixture {ι : Type u} {a : ι → β} {u : ι → bSet β} :
  (mixture a u).bval = λx, ⨆(j:ι), a j ⊓ ((u x.fst).func x.snd) ∈ᴮ u j :=
  by refl

def floris_mixture {ι : Type u} (a : ι → β) (u : ι → bSet β) : bSet β :=
  ⟨Σ(i : ι), (u i).type, λx, (u x.fst).func x.snd, λx, a x.fst ⊓ (u x.fst).bval x.snd⟩

/-- Mixing lemma, c.f. Bell's book or Lemma 1 of Hamkins-Seabold -/
lemma mixing_lemma {ι : Type u} (a : ι → β) (τ : ι → bSet β) (h_star : ∀ i j : ι, a i ⊓ a j ≤ τ i =ᴮ τ j) : ∃ x, ∀ i : ι, a i ≤ x =ᴮ τ i :=
begin
  refine ⟨mixture a τ, λ i, _⟩, rw[bSet_bool_equiv_rw],
  apply le_inf,
    {apply le_infi, intro i_z, apply deduction.mp, simp, rw[inf_supr_eq], apply supr_le,
    intro j, rw[<-inf_assoc],
    have : a i ⊓ a j ⊓ func (τ (i_z.fst)) (i_z.snd) ∈ᴮ τ j ≤ (τ i =ᴮ τ j) ⊓ func (τ (i_z.fst)) (i_z.snd) ∈ᴮ τ j,
      by {apply inf_le_inf (h_star i j), refl},
    apply le_trans this, rw[bool_equiv_symm], apply subst_congr_mem_right},
  {apply le_infi, intro i_z, rw[<-deduction], apply le_supr_of_le (sigma.mk i i_z),
  simp, apply le_supr_of_le i, apply inf_le_inf (by refl : a i ≤ a i), dsimp, cases (τ i),
  apply le_supr_of_le i_z, apply le_inf, refl, convert le_top, apply bool_equiv_refl},
end

instance bSet_full : full (bSet β) β :=
  full.mk $ λ P, sorry

/-- The axiom of weak replacement says that for every ϕ(x,y),
    for every set u, ∀ x ∈ u, ∃ y ϕ (x,y) implies there exists a set v
    which contains the image of u under ϕ. With the other axioms,
    this should be equivalent to the usual axiom of replacement. -/
theorem bSet_axiom_of_weak_replacement (ϕ : bSet β → bSet β → β) (u : bSet β) :
  (⨅(i:u.type), (u.bval i ⟹ (⨆(y : bSet β), ϕ (u.func i) y))) ⟹
  (⨆(v : bSet β), (⨅(i : u.type), u.bval i ⟹ (⨆(j:v.type), ϕ (u.func i) (v.func j)))) = ⊤ :=
begin
  simp only [bSet.bval, lattice.imp_top_iff_le, bSet.func, bSet.type],
  have := classical.axiom_of_choice (choice u.func u.bval ϕ),
  rcases this with ⟨wit, wit_property⟩, dsimp at wit wit_property,
  fapply le_supr_of_le, exact ⟨u.type, wit, λ _, ⊤⟩,
    {simp, intro i, apply le_trans (wit_property i),
     apply imp_le_of_right_le, exact le_supr (λ x, ϕ (func u i) (wit x)) i}
end

end bSet
