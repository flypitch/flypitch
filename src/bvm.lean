import fol set_theory.zfc set_theory.ordinal order.boolean_algebra order.complete_boolean_algebra tactic.rewrite tactic.monotonicity .to_mathlib tactic.monotonicity bv_prf

local infix ` ⟹ `:65 := lattice.imp

local infix ` ⇔ `:50 := lattice.biimp

-- uncomment in case of emergency
-- @[tidy] meta def big_bertha : tactic unit := `[finish]

namespace tactic.interactive
section natded_tactics
open lean.parser lean tactic tactic.interactive interactive.types interactive
local postfix `?`:9001 := optional
meta def bv_intro : parse ident_? → tactic unit
| none := propagate_tags (`[apply le_infi] >> intro1 >> tactic.skip)
| (some n) := propagate_tags (`[apply lattice.le_infi] >> tactic.intro n >> tactic.skip)

meta def ac_change (r : parse texpr) : tactic unit :=
do 
   v₁ <- mk_mvar,
   v₂ <- mk_mvar,
   refine ``(eq.mpr %%v₁ (%%v₂ : %%r)),
   gs <- get_goals,
   set_goals (list.cons v₁ list.nil),
   -- `[try{simp only [bv_eq_symm]}],
   try ac_refl,
   gs' <- get_goals,
   set_goals $ gs' ++ gs

-- example {α : Type*} [lattice.boolean_algebra α] {a₁ a₂ a₃ a₄ : α} :
--   (a₁ ⊔ a₂) ⊔ (a₃ ⊔ a₄) = ⊤
-- :=
-- begin
--   ac_change a₁ ⊔ (a₂ ⊔ a₃ ⊔ a₄) = ⊤,
-- -- α : Type ?,
-- -- _inst_1 : lattice.boolean_algebra α,
-- -- a₁ a₂ a₃ a₄ : α
-- -- ⊢ a₁ ⊔ (a₂ ⊔ a₃ ⊔ a₄) = ⊤
-- end
   
end natded_tactics
end tactic.interactive

namespace lattice
section natded
variables {β : Type*} [complete_boolean_algebra β]

lemma supr_imp_eq {ι : Type*} {s : ι → β} {b : β} :
  (⨆(i:ι), s i) ⟹ b = (⨅(i:ι), s i ⟹ b) :=
by {unfold imp, rw[neg_supr, infi_sup_eq]}

lemma bv_Or_elim  {ι : Type*} {s : ι → β} {c : β} :
(∀ i : ι, (s i ≤ c)) → ((⨆(i:ι), s i) ≤ c) :=
λ H, by apply supr_le; from H

lemma bv_And_intro {ι : Type*} {s : ι → β} {b c : β} :
(∀ i : ι, (c ≤ s i)) → (c ≤ ⨅(i:ι), s i) :=
λ H, by {apply le_infi, from H}

lemma bv_or_elim {b₁ b₂ c : β} {h : b₁ ≤ c} {h' : b₂ ≤ c} : b₁ ⊔ b₂ ≤ c :=
by apply sup_le; assumption

lemma bv_exfalso {a b : β} {h : a ≤ ⊥} : a ≤ b :=
by finish

lemma bv_cases_left {ι : Type*} {s : ι → β} {c b : β} {h : ∀ i : ι, (s i ⊓ c ≤ b)} :
  ((⨆(i:ι), s i) ⊓ c) ≤ b :=
by finish[deduction]

lemma bv_cases_right {ι : Type*} {s : ι → β} {c b : β} {h : ∀ i : ι, (c ⊓ s i ≤ b)} :
  (c ⊓ (⨆(i:ι), s i)) ≤ b :=
by {rw[inf_comm], apply bv_cases_left, finish}

lemma bv_specialize {ι : Type*} {s : ι → β} (i : ι) {b : β} {h : s i ≤ b} :
(⨅(i:ι), s i) ≤ b := infi_le_of_le i h

lemma bv_specialize_left {ι : Type*} {s : ι → β} {c b : β} (i : ι)
  {h : s i ⊓ c ≤ b} : (⨅(i:ι), s i) ⊓ c ≤ b :=
by {rw[deduction], apply bv_specialize i, rwa[<-deduction]}

lemma bv_specialize_right {ι : Type*} {s :ι → β} {c b : β} (i : ι)
  {h : c ⊓ s i ≤ b} : c ⊓ (⨅(i:ι), s i) ≤ b :=
by {rw[inf_comm], apply bv_specialize_left i, finish}
  
lemma bv_imp_elim {a b : β} : (a ⟹ b) ⊓ a ≤ b :=
by simp[imp, inf_sup_right]

lemma bv_imp_elim' {a b : β} : (a ⟹ b) ⊓ a ≤ a ⊓ b :=
by {simp[imp, inf_sup_right]}

lemma bv_and_intro {a b₁ b₂ : β} (h₁ : a ≤ b₁) (h₂ : a ≤ b₂) : a ≤ b₁ ⊓ b₂ := le_inf h₁ h₂

lemma from_empty_context {a b : β} (h : ⊤ ≤ b) : a ≤ b :=
  by refine le_trans _ h; apply le_top

lemma bv_imp_intro {a b c : β} {h : a ⊓ b ≤ c} :
  a ≤ b ⟹ c := by rwa[deduction] at h

lemma bv_have {a b c : β} (h : a ≤ b) {h' : a ⊓ b ≤ c} : a ≤ c :=
by {rw[show a = a ⊓ a, by simp], apply le_trans, apply inf_le_inf, refl, exact h, exact h'}

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


/- A β-valued model of ZFC -/

-- τ is a B-name if and only if τ is a set of pairs of the form ⟨σ, b⟩, where σ is
-- a B-name and b ∈ B.
inductive bSet (β : Type u) [complete_boolean_algebra β] : Type (u+1)
| mk (α : Type u) (A : α → bSet) (B : α → β) : bSet

namespace bSet
variables {β : Type u} [nontrivial_complete_boolean_algebra β]

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
@[reducible]def bv_eq : ∀ (x y : bSet β), β
/- ∀ x ∃ y, m x y ∧ ∀ y ∃ x, m y x, but this time in ~lattice~ -/
| ⟨α, A, B⟩ ⟨α', A', B'⟩ :=
             (⨅a : α, B a ⟹ ⨆a', B' a' ⊓ bv_eq (A a) (A' a')) ⊓
               (⨅a' : α', B' a' ⟹ ⨆a, B a ⊓ bv_eq (A a) (A' a'))

infix ` =ᴮ `:80 := bv_eq

theorem bv_eq_refl_empty : (@bv_eq β _) (empty) (empty) = ⊤ :=
  by unfold empty bv_eq;
  {simp only [lattice.inf_eq_top_iff, lattice.infi_eq_top], fsplit; intros i; cases i; cases i}

open lattice

@[simp]theorem bv_eq_refl : ∀ x, @bv_eq β _ x x = ⊤ :=
begin
  intro x, induction x, simp[bv_eq, -imp_top_iff_le], split; intros;
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

lemma mem_unfold {u v : bSet β} : u ∈ᴮ v = ⨆(i : v.type), v.bval i ⊓ u =ᴮ v.func i :=
by cases v; simp


/-- ∅ appears in empty'' with probability 0 and 1, with the higher probability winning the
    vote of membership. This demonstrates why the inequality in the following theorem is
    necessary. -/
example : ∅ ∈ᴮ empty'' = (⊤ : β) :=
  by {apply top_unique, apply le_supr_of_le ⊤, swap, exact ⟨⟨(tt)⟩⟩, finish}

theorem mem.mk {α : Type*} (A : α → bSet β) (B : α → β) (a : α) : B a ≤ A a ∈ᴮ mk α A B :=
  le_supr_of_le a $ by simp

theorem mem.mk' (x : bSet β) (a : x.type) : x.bval a ≤ x.func a ∈ᴮ x :=
by {cases x, apply le_supr_of_le a, simp}


@[simp, reducible]protected def subset : bSet β → bSet β → β
| (mk α A B) b := ⨅a:α, B a ⟹ (A a ∈ᴮ b)

infix ` ⊆ᴮ `:80 := bSet.subset

@[simp]lemma subset_unfold {x u : bSet β} : x ⊆ᴮ u = (⨅(j : x.type), x.bval j ⟹ x.func j ∈ᴮ u) :=
by induction x; dsimp; congr

@[simp]protected def insert : bSet β → β → bSet β → bSet β
| u b ⟨α, A, B⟩ := ⟨option α, λo, option.rec u A o, λo, option.rec b B o⟩

protected def insert' : bSet β → β → bSet β → bSet β
| u b ⟨α, A, B⟩ := ⟨unit ⊕ α, λ o, sum.rec (λ_, u) A o, λ o, sum.rec (λ_, b) B o⟩

@[reducible, simp]protected def insert1 : bSet β → bSet β → bSet β
| u v := bSet.insert u ⊤ v

instance insert_bSet : has_insert (bSet β) (bSet β) :=
  ⟨λ u v, bSet.insert1 u v⟩

@[simp]lemma insert_rw {y z : bSet β} : insert y z = bSet.insert y ⊤ z :=
  by refl

@[simp]theorem mem_insert {x y z : bSet β} {b : β} :
  x ∈ᴮ bSet.insert y b z = (b ⊓ x =ᴮ y) ⊔ x ∈ᴮ z :=
  by induction y; induction z; simp

theorem mem_insert1 {x y z : bSet β} : x ∈ᴮ insert y z = x =ᴮ y ⊔ x ∈ᴮ z :=
  by simp

example : {∅} =ᴮ empty'' = (⊤ : β) :=
begin
  simp[empty'', singleton, insert, has_insert.insert], simp[has_emptyc.emptyc, empty],
  refine ⟨_, by intro i; repeat{cases i}⟩, apply top_unique,
 have : ⊤ = (ulift.rec (bool.rec ⊥ ⊤) : ulift bool → β) (ulift.up tt),
   by refl,
 rw[this], apply le_supr
end

@[symm]theorem bv_eq_symm {x y : bSet β} : x =ᴮ y = y =ᴮ x :=
begin
  induction x with α A B generalizing y, induction y with α' A' B',
  suffices : ∀ a : α, ∀ a' : α', A' a' =ᴮ A a = A a =ᴮ A' a',
    by {simp[bv_eq, this, inf_comm]}, from λ _ _, by simp[x_ih ‹α›]
end

-- example {x y : bSet β} : x =ᴮ y = y =ᴮ x :=
-- begin
--   fapply le_antisymm; fapply bv_prf,
--   exact [x=ᴮy], simp, tactic.rotate 1, exact [y=ᴮx], simp,
--   induction x with α A B generalizing y, induction y with α' A' B',
--   rw[bv_eq], apply bv_cases_head,
--   apply bv_prf_and_intro, sorry
-- end

theorem bSet_bv_eq_rw (x y : bSet β) :
  x =ᴮ y = (⨅(a : x.type), x.bval a ⟹ (x.func a ∈ᴮ y))
          ⊓ (⨅(a' : y.type), (y.bval a' ⟹ (y.func a' ∈ᴮ x))) :=
 by induction x; induction y; simp[mem,bv_eq,bv_eq_symm]

theorem bSet_axiom_of_extensionality (x y : bSet β) :
(⨅(z : bSet β), (z ∈ᴮ x ⟹ z ∈ᴮ y) ⊓ (z ∈ᴮ y ⟹ z ∈ᴮ x)) ≤ x =ᴮ y :=
begin
  rw[bSet_bv_eq_rw],
  apply le_inf; apply le_infi; intro i,
  {fapply infi_le_of_le (x.func i), apply inf_le_left_of_le,
   induction x, unfold mem, simp, by apply imp_le_of_left_le; apply le_supr_of_le i;
   exact le_inf (by refl) (by rw[bv_eq_refl]; apply le_top)},
  {fapply infi_le_of_le (y.func i), apply inf_le_right_of_le,
   induction y, unfold mem, simp, by apply imp_le_of_left_le; apply le_supr_of_le i;
   exact le_inf (by refl) (by rw[bv_eq_refl]; apply le_top)},
end

theorem bv_eq_trans {x y z : bSet β} : (x =ᴮ y ⊓ y =ᴮ z) ≤ x =ᴮ z :=
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

lemma bv_eq_le_congr_right {u v w} {h : v = w} : u =ᴮ v ≤ (u =ᴮ w : β) := by rw[h]

lemma bv_eq_le_congr_left {u v w} {h : v = w} : v =ᴮ u ≤ (w =ᴮ u : β) := by rw[h]

/-- If u = v and u ∈ w, then this implies that v ∈ w -/
lemma subst_congr_mem_left {u v w : bSet β} : u =ᴮ v ⊓ u ∈ᴮ w ≤ v ∈ᴮ w :=
begin
  cases w,
  have : ∀ a : w_α, u =ᴮ v ⊓ w_B a ⊓ u =ᴮ w_A a ≤ w_B a ⊓ v =ᴮ w_A a,
    by {intro a, have := inf_le_inf (by refl : w_B a ≤ w_B a) (@bv_eq_trans _ _ v u (w_A a)),
      convert this using 1, simp[bv_eq_symm, inf_comm, inf_assoc]},
  convert supr_le_supr this, simp[inf_supr_eq], congr, ext, ac_refl
end

/-- If v = w and u ∈ v, then this implies that u ∈ w -/
lemma subst_congr_mem_right {u v w : bSet β} : (v =ᴮ w ⊓ u ∈ᴮ v) ≤ u ∈ᴮ w :=
begin
  induction v, rw[inf_supr_eq], apply supr_le, intro i,
  suffices : mk v_α ‹_› ‹_› =ᴮ w ⊓ v_B i ≤ v_A i ∈ᴮ w,
  have := le_trans (inf_le_inf this (by refl : u =ᴮ v_A i ≤ u =ᴮ v_A i)) _,
  rw[<-inf_assoc], convert this using 1,
  rw[bv_eq_symm, inf_comm], apply subst_congr_mem_left,
  rw[deduction], cases w, apply inf_le_left_of_le, apply infi_le
end

lemma bounded_quantification {v : bSet β} {ϕ : bSet β → β } {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} :
  (⨅(i_x : v.type), (v.bval i_x ⟹ ϕ (v.func i_x))) = (⨅(x : bSet β), x ∈ᴮ v ⟹ ϕ x)  :=
begin
  apply le_antisymm,
    {apply le_infi, intro x, cases v, simp, rw[supr_imp_eq],
     apply le_infi, intro i_y, apply infi_le_of_le i_y,
     rw[<-deduction,<-inf_assoc], apply le_trans, apply inf_le_inf,
     apply bv_imp_elim, refl, rw[inf_comm, bv_eq_symm], apply h_congr},
         {apply le_infi, intro i_x', apply infi_le_of_le (func v i_x'), apply imp_le_of_left_le,
     cases v, simp, apply le_supr_of_le i_x',
       apply le_inf, refl, rw[bv_eq_refl], apply le_top}
end

-- lemma bounded_quantification' {ϕ : bSet β → β } {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} {v : bSet β} :
--   (⨅(i_x : v.type), (v.bval i_x ⟹ ϕ (v.func i_x))) = (⨅(x : bSet β), x ∈ᴮ v ⟹ ϕ x)  :=
-- begin
--   apply le_antisymm,
--     {apply le_infi, intro x, cases v, simp, rw[supr_imp_eq],
--      apply le_infi, intro i_y, apply infi_le_of_le i_y,
--      rw[<-deduction,<-inf_assoc], apply le_trans, apply inf_le_inf,
--      apply bv_imp_elim, refl, rw[inf_comm, bv_eq_symm], apply h_congr},
--          {apply le_infi, intro i_x', apply infi_le_of_le (func v i_x'), apply imp_le_of_left_le,
--      cases v, simp, apply le_supr_of_le i_x',
--        apply le_inf, refl, rw[bv_eq_refl], apply le_top}
-- end


lemma subst_congr_subset_left {x v u} : ((v ⊆ᴮ u) ⊓ (x =ᴮ v) : β) ≤ (x ⊆ᴮ u) :=
begin
  simp only [subset_unfold],
  have H₁ := @bounded_quantification _ _ v (λ x, x ∈ᴮ u)
    (by {intros, apply subst_congr_mem_left}),
  have H₂ := @bounded_quantification _ _ x (λ x, x ∈ᴮ u)
    (by {intros, apply subst_congr_mem_left}),
  rw[H₁, H₂], dsimp, bv_intro z, rw[deduction],
  apply infi_le_of_le z, rw[<-deduction, <-deduction], rw[inf_assoc],
  apply le_trans, apply inf_le_inf, refl, apply subst_congr_mem_right,
  apply bv_imp_elim -- todo write tactics to make these calculations easier
end

def is_definite (u : bSet β) : Prop := ∀ i : u.type, u.bval i = ⊤

/-- ϕ (x) is true if and only if the Boolean truth-value of ϕ(x̌) is ⊤-/
/- To even state this theorem, we need to set up more general machinery for
   Boolean-valued structures and the interpretation of formulas within them -/
-- theorem check_transfer : sorry := sorry

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
  refine ⟨mixture a τ, λ i, _⟩, rw[bSet_bv_eq_rw],
  apply le_inf,
    {apply le_infi, intro i_z, apply deduction.mp, simp, rw[inf_supr_eq], apply supr_le,
    intro j, rw[<-inf_assoc],
    have : a i ⊓ a j ⊓ func (τ (i_z.fst)) (i_z.snd) ∈ᴮ τ j ≤ (τ i =ᴮ τ j) ⊓ func (τ (i_z.fst)) (i_z.snd) ∈ᴮ τ j,
      by {apply inf_le_inf (h_star i j), refl},
    apply le_trans this, rw[bv_eq_symm], apply subst_congr_mem_right},
  {apply le_infi, intro i_z, rw[<-deduction], apply le_supr_of_le (sigma.mk i i_z),
  simp, apply le_supr_of_le i, apply inf_le_inf (by refl : a i ≤ a i), dsimp, cases (τ i),
  apply le_supr_of_le i_z, apply le_inf, refl, simp}
end

-- TODO(jesse) try proving mixing_lemma with floris_mixture and see if anything goes wrong

/-- In particular, the mixing lemma applies when the weights (a_i) form an antichain and the indexing is injective -/
lemma h_star_of_antichain_injective {ι : Type u} {a : ι → β} {τ : ι → bSet β} {h_anti : antichain (a '' set.univ)} {h_inj : function.injective a} :
  ∀ i j : ι, a i ⊓ a j ≤ τ i =ᴮ τ j :=
begin
  intros i j, by_cases a i = a j, simp[h_inj h],
  have := h_anti _ _ _ _ h, simp[this], tidy
end

/- Note: this is the special condition assumed of indexed antichains by Bell-/
lemma h_star_of_antichain_index {ι : Type u} {a : ι → β} {τ : ι → bSet β} {h_anti : antichain (a '' set.univ)} {h_index : ∀ i j : ι, i ≠ j → a i ⊓ a j = ⊥} :
  ∀ i j : ι, a i ⊓ a j ≤ τ i =ᴮ τ j :=
  λ i j, by {haveI : decidable_eq ι := λ _ _,
  by apply classical.prop_decidable _,
    by_cases i = j, simp[h], finish[h_index i j]}

/- The next two lemmas use the fact that β : Type u to extract a small set witnessing quantification over all of bSet β -/

/- i.e., in bSet β, any existential quantification is equivalent to a bounded existential quantification. this is one place where it's crucial that β lives in the type universe out of which bSet β is being built -/
section smallness
variable {ϕ : bSet β → β}

@[reducible, simp]noncomputable def fiber_lift (b : ϕ '' set.univ) :=
classical.indefinite_description (λ a : bSet β, ϕ a = b.val)
  begin cases b.property, use w, exact h.right end

noncomputable def B_small_witness : bSet β :=
⟨ϕ '' set.univ, λ b, (fiber_lift b).val, λ _, ⊤⟩

@[simp]lemma B_small_witness_spec : ∀ b, ϕ ((@B_small_witness _ _ ϕ).func b) = b.val :=
  λ b, (fiber_lift b).property

lemma B_small_witness_supr : (⨆(x : bSet β), ϕ x) = ⨆(b : (@B_small_witness _ _ ϕ).type), ϕ (B_small_witness.func b) :=
begin
 apply le_antisymm,
 apply supr_le, intro x, let b : type B_small_witness := by {use ϕ x, simp, exact ⟨x, rfl⟩},
 fapply le_supr_of_le, exact b, have := B_small_witness_spec b, dsimp at this, rw[this],
 apply supr_le, intro b, apply le_supr_of_le, swap, exact (fiber_lift b).val, refl
end

@[reducible, simp]def not_b (b : β) : set β := λ y, y ≠ b

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

lemma down_set_mono_supr {a b} {h : a ≺ b} {s : type (@B_small_witness _ _ ϕ) → β} :
 (⨆(i ∈ down_set r a), s i) ≤ (⨆(i ∈ down_set r b), s i) :=
begin
  apply supr_le_supr, intro i, apply supr_le, intro H, apply le_supr_of_le,
  apply down_set_trans, exact h, exact H, refl
end

lemma down_set'_mono_supr {a b} {h : a ≺ b} {s : type (@B_small_witness _ _ ϕ) → β} :
 (⨆(i ∈ down_set' r a), s i) ≤ (⨆(i ∈ down_set' r b), s i) :=
begin
  apply supr_le_supr, intro i, apply supr_le, intro H,
 apply le_supr_of_le,
  cases H, apply or.inr, rw[H], exact h, apply or.inr,
  apply down_set_trans, exact h, exact H, refl
end

def witness_antichain : _ → β :=
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
-- @[reassoc]lemma sup_reassoc {a b c : β} : a ⊔ (b ⊔ c) = a ⊔ b ⊔ c :=
-- by ac_refl

-- @[reassoc]lemma inf_reassoc {a b c : β} : a ⊓ (b ⊓ c) = a ⊓ b ⊓ c :=
-- by ac_refl

-- @[reassoc]lemma abcd_reassoc_sup {a b c d : β} : (a ⊔ b) ⊔ (c ⊔ d) = a ⊔ b ⊔ c ⊔ d :=
-- by rw[sup_reassoc]

-- @[reassoc]lemma abcd_reassoc_inf {a b c d : β} : (a ⊓ b) ⊓ (c ⊓ d) = a ⊓ b ⊓ c ⊓ d :=
-- by rw[inf_reassoc]

-- lemma abcd_rw_cabd_sup {a b c d : β} : a ⊔ b ⊔ c ⊔ d = c ⊔ b ⊔ a ⊔ d :=
-- by ac_refl

-- lemma abcd_rw_cabd_inf {a b c d : β} : a ⊓ b ⊓ c ⊓ d = c ⊓ b ⊓ a ⊓ d :=
-- by ac_refl

-- lemma abcd_rw_bcad_inf {a b c d : β} : a ⊓ b ⊓ c ⊓ d = b ⊓ c ⊓ a ⊓ d :=
-- by ac_refl

def witness_antichain_index : ∀ {i j}, i ≠ j → (@witness_antichain _ _ ϕ r _) i ⊓ (@witness_antichain _ _ ϕ r _) j = ⊥ :=
λ x y h_neq,
begin
  dsimp[witness_antichain], simp[sub_eq, neg_supr], 
  apply bot_unique, cases dichotomy_of_neq r _ _ h_neq,
  {ac_change (y.val ⊓ ⨅ (i : {x_1 // x_1 ∈ down_set r x}), -(i.val).val) ⊓
    (x.val ⊓ ⨅ (i : {x // x ∈ down_set r y}), -(i.val).val) ≤ ⊥,
    apply inf_le_right_of_le,
  rw[inf_comm, deduction], apply infi_le_of_le,
  swap, use x, exact h, simp},
  
  {ac_change (⨅ (i : {x_1 // x_1 ∈ down_set r x}), -(i.val).val) ⊓ y.val ⊓
      (x.val ⊓ ⨅ (i : {x // x ∈ down_set r y}), -(i.val).val) ≤ ⊥,
      apply inf_le_left_of_le, rw[deduction], apply infi_le_of_le, swap, exact ⟨y, h⟩, simp}
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
     let A := _, change ⊤ ≤ (A ⊔ _ : β), apply le_trans (by simp : ⊤ ≤ A ⊔ -A), apply sup_le_sup, refl, dsimp[A],
   rw[lattice.neg_neg], 
   apply supr_le, intro j,
   apply le_trans (this_ih j j.property), unfold witness_antichain,
   apply supr_le_supr, intro i', apply supr_le, intro H',
   cases H', subst H', apply le_supr_of_le, exact j.property, refl,
   apply le_supr_of_le, apply down_set_trans, exact j.property, exact H',
   refl
end
end smallness


lemma maximum_principle (ϕ : bSet β → β) (h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y) : ∃ u, (⨆(x:bSet β), ϕ x) = ϕ u :=
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

lemma maximum_principle_verbose {ϕ : bSet β → β} {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} {b : β} (h_eq_top L : (⨆(x:bSet β), ϕ x) = b) : ∃ u, ϕ u = b :=
 by cases maximum_principle ϕ h_congr with w h; from ⟨w, by finish⟩

/-- "∃ x ∈ u, ϕ x implies ∃ x : bSet β, ϕ x", but this time, say it in Boolean -/
lemma weaken_ex_scope {α : Type*} (A : α → bSet β) (ϕ : bSet β → β)  : (⨆(a : α), ϕ (A a)) ≤ (⨆(x : bSet β), ϕ x) :=
supr_le $ λ a, le_supr_of_le (A a) (by refl)

lemma maximum_principle_bounded_top {ϕ : bSet β → β} {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} {α : Type*} {A : α → bSet β} (h_eq_top : (⨆(a:α), ϕ (A a)) = ⊤) : ∃ u, ϕ u = ⊤ :=
@maximum_principle_verbose β (by apply_instance) ϕ h_congr ⊤ (by {have := weaken_ex_scope A ϕ, finish}) (by {have := weaken_ex_scope A ϕ, finish})

/-- Convert a Boolean-valued ∀∃-statement into a Prop-valued ∀∃-statement
  Given A : α → bSet β, a binary function ϕ : bSet β → bSet β → β, a truth-value assignment
  B : α → β, ∀ i : α, there exists a y_i : bSet β, such that
  (B i ⟹ ϕ (A i) y_i) ≥ ⨅(i:α), B i ⟹ ⨆(y : bSet β), ϕ(A i, bSet β)

  A more verbose, but maybe clearer way to see this is:
  if there is an equality (⨅i-⨆j body i j) = b,
  then for all i, there exists j, such that body i j ≥ b

  This is a consequence of the maximum principle.
-/
lemma AE_convert {α β : Type*} [nontrivial_complete_boolean_algebra β] (A : α → bSet β)
  (B : α → β) (ϕ : bSet β → bSet β → β) (h_congr : ∀ x y z, x =ᴮ y ⊓ ϕ z x ≤ ϕ z y) :
  ∀ i : α, ∃ y : bSet β, (⨅(j:α), (B j ⟹ ⨆(z : bSet β), ϕ (A j) z)) ≤ (B i ⟹ ϕ (A i) y) :=
λ i,
  by {have := maximum_principle (λ y, ϕ (A i) y)
                (by {intros x y, apply h_congr}),
      rcases this with ⟨u', H'⟩, use u', apply infi_le_of_le i,
      apply imp_le_of_right_le, from le_of_eq H'}  

section check_names
/- `check` is the canonical embedding of pSet into bSet.
note that a check-name is not only definite, but recursively definite
-/
@[simp]def check : (pSet : Type (u+1)) → bSet β
| ⟨α,A⟩ := ⟨α, λ a, check (A a), λ a, ⊤⟩

postfix `̌ `:90 := check

example : let x := pSet.empty in (x̌ : bSet β) = bSet.empty :=
  by dsimp[check, pSet.empty, bSet.empty]; simp; fsplit; ext1; repeat{cases x}

lemma check_bv_eq_top_of_equiv {x y : pSet} :
  pSet.equiv x y → x̌ =ᴮ y̌ = (⊤ : β) :=
begin
  induction x generalizing y, cases y,
  dsimp[check], simp only [pSet.equiv, lattice.top_le_iff, bSet.check,
  lattice.top_inf_eq, lattice.imp_top_iff_le, lattice.inf_eq_top_iff, lattice.infi_eq_top],
  intros a, cases a, split; intro i;
  apply top_unique; [rcases a_left i with ⟨w, h⟩, rcases a_right i with ⟨w,h⟩];
  apply le_supr_of_le w; simp only [lattice.top_le_iff, bSet.check]; apply (x_ih _); exact h
end

lemma check_bv_eq_bot_of_not_equiv {x y : pSet} :
  (¬ pSet.equiv x y) → (x̌ =ᴮ y̌) = (⊥ : β) :=
begin
  induction x generalizing y, cases y, dsimp[check], intro H, apply bot_unique,
  cases pSet.not_equiv H with H H; cases H with w H_w;
  [apply inf_le_left_of_le, apply inf_le_right_of_le]; apply infi_le_of_le (w); simp[-le_bot_iff];
  intro a'; rw[le_bot_iff]; apply x_ih; apply H_w
end

lemma check_bv_eq_dichotomy (x y : pSet) :
  (x̌ =ᴮ y̌ = (⊤ : β)) ∨ (x̌ =ᴮ y̌ = (⊥ : β)) :=
begin
  haveI : decidable (pSet.equiv x y) := by apply classical.prop_decidable,
  by_cases pSet.equiv x y; [left, right];
  [apply check_bv_eq_top_of_equiv, apply check_bv_eq_bot_of_not_equiv]; assumption
end

lemma check_bv_eq_iff {x y : pSet} 
: pSet.equiv x y ↔ x̌ =ᴮ y̌ = (⊤ : β) :=
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

end check_names

/-- The axiom of weak replacement says that for every ϕ(x,y),
    for every set u, ∀ x ∈ u, ∃ y ϕ (x,y) implies there exists a set v
    which contains the image of u under ϕ. With the other axioms,
    this should be equivalent to the usual axiom of replacement. -/
theorem bSet_axiom_of_weak_replacement (ϕ : bSet β → bSet β → β) (h_congr : ∀ x y z, x =ᴮ y ⊓ ϕ z x ≤ ϕ z y) (u : bSet β) :
  (⨅(i:u.type), (u.bval i ⟹ (⨆(y : bSet β), ϕ (u.func i) y))) ⟹
  (⨆(v : bSet β), (⨅(i : u.type), u.bval i ⟹ (⨆(j:v.type), ϕ (u.func i) (v.func j)))) = ⊤ :=
begin
  simp only [bSet.bval, lattice.imp_top_iff_le, bSet.func, bSet.type],
  rcases (classical.axiom_of_choice (AE_convert u.func u.bval ϕ h_congr)) with ⟨wit, wit_property⟩, dsimp at wit wit_property,
  fapply le_supr_of_le, exact ⟨u.type, wit, λ _, ⊤⟩,
    {simp, intro i, apply le_trans (wit_property i),
     apply imp_le_of_right_le, exact le_supr (λ x, ϕ (func u i) (wit x)) i}
end

/-- The boolean-valued unionset operator -/
def bv_union (u : bSet β) : bSet β :=
  ⟨Σ(i : u.type), (u.func i).type, λ x, (u.func x.1).func x.2,
       λ x, ⨆(y : u.type), (u.func x.1).func x.2 ∈ᴮ (u.func y)⟩

lemma func_cast {u x : bSet β} {i_y : u.type} {α : Type u} {A : α → bSet β} {B : α → β} {h : func u i_y = mk α A B} {i_x' : α} : func (func u i_y) (eq.mpr (by rw[h]; refl) i_x') = A i_x' :=
begin
  change _ = (mk α A B).func i_x',
  have : func (mk α A B) (eq.mpr rfl i_x') = func (mk α A B) i_x', by refl,
  convert this
end

theorem bSet_axiom_of_union : (⨅ (u : bSet β), (⨆(v : _), ⨅(x : _), (x ∈ᴮ v ⇔ (⨆(y : u.type), x ∈ᴮ u.func y)))) = ⊤ :=
begin
  simp only [bSet.mem, lattice.biimp, bSet.func, lattice.infi_eq_top, bSet.type], intro u,
  apply top_unique, apply le_supr_of_le (bv_union u),
  simp only [lattice.top_le_iff, bSet.mem, lattice.imp_top_iff_le,
  lattice.inf_eq_top_iff, bSet.func, lattice.le_infi_iff, bSet.type, lattice.supr_le_iff],
  intros x, fsplit, work_on_goal 1 { intros i_y },
  {dsimp[bv_union], apply supr_le, rintro ⟨i_y', i_x'⟩,
   rw[supr_inf_eq], apply supr_le, intro i_y'', dsimp,
   apply le_supr_of_le i_y'', cases (func u i_y''),
   unfold mem, rw[supr_inf_eq], apply supr_le_supr, intro j,
   rw[inf_assoc], apply inf_le_inf, refl, rw[inf_comm], apply bv_eq_trans},
  {unfold bv_union, dsimp, destruct (func u i_y), intros α A B h, rw[h], apply supr_le, intro i_x',
   fapply le_supr_of_le, use i_y, rw[h], exact i_x', dsimp,
   rw[supr_inf_eq], apply le_supr_of_le i_y, apply inf_le_inf,
   swap, apply bv_eq_le_congr_right, apply func_cast.symm, repeat{assumption},
   have := @mem.mk β _ α A B i_x', convert this, apply func_cast, repeat{assumption}}
end

@[reducible, simp]def set_of_indicator {u : bSet β} (f : u.type → β) : bSet β :=
  ⟨u.type, u.func, f⟩

@[reducible, simp]def set_of_indicator' {u : bSet β} (f : u.type → β) : bSet β :=
  ⟨u.type, u.func, λ i, f i ⊓ u.bval i⟩

def bv_powerset (u : bSet β) : bSet β :=
⟨u.type → β, λ f, set_of_indicator f, λ f, set_of_indicator f ⊆ᴮ u⟩

def bv_powerset' (u : bSet β) : bSet β :=
⟨u.type → β, λ f, set_of_indicator' f, λ f, ⊤⟩

--TODO (jesse) try proving bv_powerset and bv_powerset' are equivalent

example {u : bSet β} : bv_powerset u =ᴮ bv_powerset' u = ⊤ :=
begin
  apply top_unique, apply le_trans, swap, apply bSet_axiom_of_extensionality,
  bv_intro z, apply le_inf; apply bv_imp_intro; simp[top_inf_eq],
  {unfold bv_powerset, dsimp, apply supr_le, intro f,
  unfold bv_powerset', simp, apply le_supr_of_le f,
   refine le_trans _ (by apply bSet_axiom_of_extensionality),
   bv_intro z',
   have := @bounded_quantification _ _ (set_of_indicator f) (λ x, x ∈ᴮ u), dsimp[set_of_indicator] at this, rw[this],
   rw[deduction], apply infi_le_of_le z', rw[supr_imp_eq],
   apply bv_imp_intro, apply le_inf, apply bv_imp_intro,
   ac_change  (⨅ (i : type u), f i ⊓ z' =ᴮ func u i ⟹ z' ∈ᴮ u) ⊓ (z =ᴮ mk (type u) (func u) f ⊓ z' ∈ᴮ z) ≤ z' ∈ᴮ mk (type u) (func u) (λ (i : type u), f i ⊓ bval u i),
   apply le_trans, apply inf_le_inf, refl, apply subst_congr_mem_right,
   rw[inf_comm], rw[deduction], apply supr_le, intro i',
   rw[<-deduction], apply le_supr_of_le i', dsimp,
   repeat{apply le_inf}, apply inf_le_left_of_le, apply inf_le_left_of_le, refl,
   repeat{sorry}

},
  {sorry}
end

theorem bSet_axiom_of_powerset : (⨅(u : bSet β), ⨆(v : _), ⨅(x : bSet β), x∈ᴮ v ⇔ ⨅(y : x.type), x.bval y ⟹ (x.func y ∈ᴮ u)) = ⊤:=
begin
  simp only [bSet.bval, bSet.mem, lattice.biimp, bSet.func, lattice.infi_eq_top, bSet.type],
  intro u, apply top_unique, apply le_supr_of_le (bv_powerset u),
  apply le_infi, intro x, apply le_inf,
  {rw[<-deduction, top_inf_eq], 
   unfold bv_powerset, apply supr_le, intro χ,
   suffices : ((set_of_indicator χ) ⊆ᴮ u ⊓ (x =ᴮ (set_of_indicator χ)) : β) ≤ x ⊆ᴮ u,
     by {convert this, simp},
   apply subst_congr_subset_left},

  {simp, have := @bounded_quantification _ _ x (λ y, (y ∈ᴮ u)) (by {intros x y, apply subst_congr_mem_left}), rw[this],
  dsimp,
  unfold bv_powerset, simp, fapply le_supr_of_le,
  from λ i, u.func i ∈ᴮ x,  have this' := @bounded_quantification _ _ (set_of_indicator (λ y, (u.func y ∈ᴮ x))) (λ y, (y ∈ᴮ u)) (by {intros x y, apply subst_congr_mem_left}), dsimp at this', rw[this'],
  apply le_inf, bv_intro a', apply infi_le_of_le a', rw[supr_imp_eq],
  apply le_infi, intro i_y, apply imp_le_of_left_right_le, swap, refl,
  rw[inf_comm, bv_eq_symm], apply subst_congr_mem_left,
  
  rw[bSet_bv_eq_rw], apply le_inf,
  {conv {to_rhs, dsimp}, have := @bounded_quantification _ _ x (λ y, ⨆ (a' :    type u), func u a' ∈ᴮ x ⊓ y =ᴮ func u a'), rw[this], swap,
  intros a₁ a₂, dsimp, rw[inf_supr_eq], apply supr_le, intro i,

  apply le_supr_of_le i,
  ac_change (a₂ =ᴮ a₁ ⊓  a₁ =ᴮ func u i) ⊓ func u i ∈ᴮ x ≤ func u i ∈ᴮ x ⊓ a₂ =ᴮ func u i, rw[bv_eq_symm], ac_refl,
  
  apply le_trans, apply inf_le_inf, apply bv_eq_trans, refl, rw[inf_comm],
  
  {bv_intro a₁, dsimp, apply infi_le_of_le a₁, rw[<-deduction],
   apply le_trans, apply bv_imp_elim', rw[inf_comm, deduction],
   rw[mem_unfold], apply supr_le, intro i, rw[<-deduction],
   apply le_supr_of_le i,
   apply le_inf, rw[inf_assoc], apply inf_le_right_of_le,
   apply subst_congr_mem_left,
   ac_change a₁ =ᴮ func u i ⊓ (bval u i ⊓ a₁ ∈ᴮ x) ≤ a₁ =ᴮ func u i,
   apply inf_le_left_of_le, refl}},

   {have := @bounded_quantification _ _ (set_of_indicator (λ y, func _ y ∈ᴮ x)) (λ y, y ∈ᴮ x), rw[this], swap, simp[subst_congr_mem_left],
   bv_intro a₁, apply infi_le_of_le a₁,
   unfold set_of_indicator, dsimp, rw[supr_imp_eq],
   bv_intro i, apply from_empty_context,
   rw[inf_comm, bv_eq_symm], simp[subst_congr_mem_left]}},
end

@[simp, reducible]def axiom_of_infinity_spec (u : bSet β) : β :=
  (∅∈ᴮ u) ⊓ (⨅(i_x : u.type), ⨆(i_y : u.type), (u.func i_x ∈ᴮ u.func i_y))

theorem bSet_axiom_of_infinity : (⨆(u : bSet β), axiom_of_infinity_spec u) = ⊤ :=
begin
  simp, apply top_unique, apply le_supr_of_le, repeat{sorry}
end -- maybe we can just define boolean-valued ω in this case directly

theorem bSet_axiom_of_regularity (ϕ : bSet β → β) (h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y) :
  (⨅(x : bSet β), ((⨅(y : bSet β), y ∈ᴮ x ⟹ ϕ y) ⟹ ϕ x)) ⟹ (⨅(x : bSet β), ϕ x) = ⊤ :=
begin
  apply top_unique, apply bv_imp_intro, rw[top_inf_eq],
  apply le_infi, intro x, let b := _, change b ≤ _,
  induction x with α A B ih, dsimp at *,
  have : b ≤ ⨅(i_y:α), B i_y ⟹ ϕ (A i_y),
    by {bv_intro i_y, specialize ih i_y, apply le_trans ih,
    rw[<-deduction], apply inf_le_left},
  have h := @bounded_quantification _ _ (mk α A B) ϕ h_congr,
  simp only with cleanup at h, rw[h] at this, 
  -- simp only with cleanup at this, rw[this],
  apply bv_have this,
  have : b ≤ (⨅ (y : bSet β), (y) ∈ᴮ (mk α A B) ⟹ ϕ (y)) ⟹ ϕ (mk α A B),
    by {apply bv_specialize (mk α A B), refl},
  rw[deduction], apply le_trans this, rw[<-deduction], apply bv_imp_elim
end

end bSet
