/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
import .bfol .forcing .forcing_CH

open lattice

open bSet

open fol
local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`:0) := l

local infixr ` ⟹' `:65 := lattice.imp
local prefix `∃'` := bd_ex
local prefix `∼` := bd_not
local infixr ` ⊓' `:70 := bd_and
local infixr ` ⊔' `:70 := bd_or

local infix ` ⟹'' `:62 := bd_imp

local infix ` ⇔' `:50 := lattice.biimp

-- local infix ` ⇔ `:61 := bd_biimp

universe u

section ZFC
inductive ZFC_rel : ℕ → Type 1
| ε : ZFC_rel 2

inductive ZFC_func : ℕ → Type 1
| emptyset : ZFC_func 0
| pr : ZFC_func 2
| ω : ZFC_func 0
| P : ZFC_func 1
| Union : ZFC_func 1

def L_ZFC : Language.{1} :=
{ functions := ZFC_func,
  relations := ZFC_rel }

end ZFC

section ZFC
variables {β : Type 0} [nontrivial_complete_boolean_algebra β]

def bSet_model_fun_map : Π {n : ℕ}, L_ZFC.functions n → dvector (bSet β) n → bSet β :=
begin
  intros n S, induction S,
  from λ _, bSet.empty,
  from λ x, by {cases x, refine bSet.pair x_x _, cases x_xs, from x_xs_x},
  from λ _, bSet.omega,
  from λ x, by {cases x, exact bv_powerset x_x},
  from λ x, by {cases x, from bv_union ‹_›}
end

def bSet_model_rel_map : Π {n : ℕ}, L_ZFC.relations n → dvector (bSet β) n → β :=
begin
  intros n R, induction R,
  intro x, cases x, cases x_xs,
  from x_x ∈ᴮ x_xs_x
end

variable (β)
def V : bStructure L_ZFC (β) :=
{ carrier := (bSet β),
  fun_map := by apply bSet_model_fun_map,
  rel_map := by apply bSet_model_rel_map,
  eq := bv_eq,
  eq_refl := bv_eq_refl,
  eq_symm := by apply bv_eq_symm,
  eq_trans := by apply bv_eq_trans,
  fun_congr :=
  begin
    intros n F, cases F,
      {intros x y, cases x, cases y, simp},
      tactic.rotate 1,
      {intros x y, cases x, cases y, simp},
      {intros x y, cases x, cases y, cases x_xs, cases y_xs,
        change (_ ⊓ _ : β) ≤ (bv_powerset _) =ᴮ (bv_powerset _), simp,
        tidy_context, apply bv_powerset_congr ‹_› },
      {intros x y, cases x, cases y, cases x_xs, cases y_xs,
        change (_ ⊓ _ : β) ≤ (bv_union _) =ᴮ (bv_union _), simp,
        tidy_context, from bv_union_congr ‹_›},
      {intros x y, cases x, cases y, cases x_xs, cases y_xs,
        change (_ ⊓ (_ ⊓ _) : β) ≤ pair x_x x_xs_x =ᴮ pair y_x y_xs_x,
        cases x_xs_xs, cases y_xs_xs, simp }
  end,
  rel_congr :=
  begin
    intros n R, cases R, intros x y,
    cases x, cases y, cases x_xs, cases y_xs,
    cases x_xs_xs, cases y_xs_xs,
    change ((_ ⊓ _) ⊓ (_ ∈ᴮ _) : β) ≤ (_ ∈ᴮ _), simp,
    tidy_context, apply mem_congr; from ‹_›
  end}

@[simp] lemma carrier_V : ↥(V β) = bSet β := rfl

@[simp]lemma V_forall {C : (V β) → β} : (⨅(x : V β), C x) = (⨅(x : bSet β), C x) := rfl

@[simp]lemma V_exists {C : (V β) → β} : (⨆(x : V β), C x) = (⨆(x : bSet β), C x) := rfl

@[simp]lemma V_eq {a b} : (V β).eq a b = a =ᴮ b := rfl

@[instance]lemma V_β_nonempty : nonempty (V β) := ⟨bSet.empty⟩

lemma alpha_equiv₁ {C : (bSet β) → β} : (⨅(x : bSet β), C x) = ⨅(y : bSet β), C y := rfl
lemma alpha_equiv₂ {C : (bSet β) → β} : (⨆(x : bSet β), C x) = ⨆(y : bSet β), C y := rfl

def emptyset {n} : bounded_term L_ZFC n := bd_const ZFC_func.emptyset

notation `∅'` := emptyset

def omega {n} : bounded_term L_ZFC n := bd_const ZFC_func.ω

notation `ω'` := omega

def Powerset {n} : bounded_term L_ZFC n → bounded_term L_ZFC n := bd_app (bd_func ZFC_func.P)

notation `P'` := Powerset

def mem {n} (t₁ t₂ : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
@bounded_formula_of_relation L_ZFC 2 n ZFC_rel.ε t₁ t₂

local infix ` ∈'`:100 := _root_.mem

def pair' {n} (t₁ t₂ : bounded_term L_ZFC n) : bounded_term L_ZFC n :=
@bounded_term_of_function L_ZFC 2 n ZFC_func.pr t₁ t₂

def union' {n} : bounded_term L_ZFC n → bounded_term L_ZFC n := bd_app (bd_func ZFC_func.Union)

notation `⋃'` := union'

local prefix `&'`:max := bd_var


@[simp] lemma boolean_realize_bounded_formula_mem {n} {v : dvector (V β) n}
  (t₁ t₂ : bounded_term L_ZFC n) :
  boolean_realize_bounded_formula v (t₁ ∈' t₂) ([]) =
  boolean_realize_bounded_term v t₁ ([]) ∈ᴮ boolean_realize_bounded_term v t₂ ([]) :=
by refl

@[simp] lemma boolean_realize_bounded_term_Union {n} {v : dvector (V β) n}
  (t : bounded_term L_ZFC n) :
  boolean_realize_bounded_term v (⋃' t) ([]) =
  bv_union (boolean_realize_bounded_term v t ([])) :=
by refl

@[simp] lemma boolean_realize_bounded_term_Powerset {n} {v : dvector (V β) n}
  (t : bounded_term L_ZFC n) :
  boolean_realize_bounded_term v (P' t) ([]) =
  bv_powerset (boolean_realize_bounded_term v t ([])) :=
by refl

@[simp] lemma boolean_realize_bounded_term_omega {n} {v : dvector (V β) n} :
  boolean_realize_bounded_term v ω' ([]) = bSet.omega :=
by refl

@[simp] lemma boolean_realize_bounded_term_emptyset {n} {v : dvector (V β) n} :
  boolean_realize_bounded_term v ∅' ([]) = bSet.empty :=
by refl

@[simp]lemma boolean_realize_bounded_term_pair {n} {v : dvector (V β) n}
  (t₁ t₂ : bounded_term L_ZFC n) :  boolean_realize_bounded_term v (pair' t₁ t₂) ([]) =
  pair (boolean_realize_bounded_term v t₁ ([])) (boolean_realize_bounded_term v t₂ ([])) :=
by refl

@[simp] lemma fin_0 {n : ℕ} : (0 : fin (n+1)).1 = 0 := by refl
@[simp] lemma fin_1 {n : ℕ} : (1 : fin (n+2)).1 = 1 := by refl
@[simp] lemma fin_2 {n : ℕ} : (2 : fin (n+3)).1 = 2 := by refl
@[simp] lemma fin_3 {n : ℕ} : (3 : fin (n+4)).1 = 3 := by refl

def axiom_of_emptyset : sentence L_ZFC := ∀' (∼(&0 ∈' ∅'))

lemma bSet_models_emptyset : ⊤ ⊩[V β] axiom_of_emptyset :=
by {change ⊤ ≤ _, simp[axiom_of_emptyset, -top_le_iff], intro x, from empty_spec}

-- axiom of ordered pairs
-- ∀x y z w, (x, y) = (z, w) ↔ x = z ∧ y = w
def axiom_of_ordered_pairs : sentence L_ZFC :=
 ∀' ∀' ∀' ∀'(((pair' &'3 &'2 ≃ pair' &'1 &'0)) ⇔ (&'3 ≃ &'1 ⊓ &'2 ≃ &'0))

lemma bSet_models_ordered_pairs : ⊤ ⊩[V β] axiom_of_ordered_pairs :=
begin
  change ⊤ ≤ _, simp[axiom_of_ordered_pairs], intros a b x y, tidy,
  from eq_of_eq_pair_left, from eq_of_eq_pair_right
end

-- axiom of extensionality
-- ∀ x y, (∀ z, (z ∈ x ↔ z ∈ y)) → x = y
def axiom_of_extensionality : sentence L_ZFC :=
∀' ∀' (∀'(&'0  ∈' &'2 ⇔  &'0 ∈' &'1) ⟹ (&1 ≃ &0))

lemma bSet_models_extensionality : ⊤ ⊩[V β] axiom_of_extensionality :=
by { simp [forced_in, axiom_of_extensionality], exact bSet_axiom_of_extensionality }

-- axiom schema of "strong" collection
-- For every formula `ϕ(x,y,p)` with (at most) `n+2` free variables (`p` is a vector of length `n`),
-- ∀ p ∀ A, (∀ x ∈ A, ∃ y, ϕ(x,y,p)) ⟹
--  (∃ B, (∀ x ∈ A, ∃ y ∈ B, ϕ(x,y,p)) ∧ ∀ y ∈ B, ∃ x ∈ A, ϕ(x,y,p))
def axiom_of_collection {n} (ϕ : bounded_formula L_ZFC (n+2)) : sentence L_ZFC :=
bd_alls (n+1) $ (∀' (&'0 ∈' &'1 ⟹ ∃' (ϕ ↑' 1 # 2))) ⟹
(∃' (∀'(&'0 ∈' &'2 ⟹ ∃' (&'0 ∈' &'2 ⊓ (ϕ ↑' 2 # 2))) ⊓
     ∀'(&'0 ∈' &'1 ⟹ ∃' (&'0 ∈' &'3 ⊓' ((ϕ ↑' 3 # 2)[&'1/0] : _)))))

lemma lift2_helper {L n l} (f : bounded_preformula L n l) {k} (m : ℕ) :
  f ↑' (k+2) # m = ((f ↑' (k+1) # m) ↑' 1 # m : _) :=
by { ext, simp only [lift_bounded_formula_fst], rw [lift_formula_at2_medium], refl, linarith }

lemma B_ext_left_realize_bounded_formula {n : ℕ} (ϕ : bounded_formula L_ZFC (n + 1)) (xs : dvector (V β) n) : ∀ (x y : V β), x =ᴮ y ⊓ (boolean_realize_bounded_formula (x::xs) ϕ dvector.nil) ≤ boolean_realize_bounded_formula (y::xs) ϕ dvector.nil :=
begin
  intros x y,
  suffices : (x =ᴮ y = ⨅ (m : fin (n+1)), (V β).eq ((x::xs).nth _ m.is_lt) ((y::xs).nth _ m.is_lt)),
    by {rw this, apply boolean_realize_bounded_formula_congr, apply_instance},
  refine le_antisymm _ _,
    { apply le_infi, rintro ⟨m,Hm⟩,
      cases m,
        { refl },
        { rw [dvector.nth_cons, dvector.nth_cons],
          {exact bSet.bv_refl, { exact nat.lt_of_succ_lt_succ Hm }},
      }},
    { tidy_context, exact a ⟨0, dec_trivial⟩ }
end

lemma B_ext_right_realize_bounded_formula {n : ℕ} (ϕ : bounded_formula L_ZFC (n + 2)) (xs : dvector (V β) n) : ∀ (x y z : V β), x =ᴮ y ⊓ (boolean_realize_bounded_formula (z::x::xs) ϕ dvector.nil) ≤ boolean_realize_bounded_formula (z::y::xs) ϕ dvector.nil :=
begin
  intros x y z,
  suffices : (x =ᴮ y = ⨅ (m : fin (n+2)), (V β).eq ((z::x::xs).nth _ m.is_lt) ((z::y::xs).nth _ m.is_lt)),
    by {rw this, apply boolean_realize_bounded_formula_congr, apply_instance},
  refine le_antisymm _ _,
    { apply le_infi, rintro ⟨m,Hm⟩,
      cases m,
        { exact bSet.bv_refl },
        { cases m,
          { refl },
          { repeat {rw dvector.nth_cons},
            { exact bSet.bv_refl, apply nat.lt_of_succ_lt_succ,
              apply nat.lt_of_succ_lt_succ, from ‹_› }} }},
    { tidy_context, exact a ⟨1, dec_trivial⟩ }
end

lemma bSet_models_collection {n} (ϕ : bounded_formula L_ZFC (n+2)) : ⊤ ⊩[V β] axiom_of_collection ϕ :=
begin
  change ⊤ ≤ _, simp only [axiom_of_collection, boolean_realize_sentence_bd_alls],
  bv_intro xs, cases xs with _ u xs,
  simp only
    [ boolean_realize_bounded_formula_and,
      boolean_realize_bounded_term, imp_top_iff_le,
      boolean_realize_bounded_formula_ex, top_le_iff,
      boolean_realize_bounded_formula, boolean_realize_formula_insert_lift2,
      lift2_helper, boolean_realize_subst_formula0, fin_2 ],
  have := bSet_axiom_of_collection
            (λ a b : V β, boolean_realize_bounded_formula (b :: a :: xs) ϕ ([])) _ _ u,
  simp only [lattice.top_le_iff, bSet.mem, lattice.imp_top_iff_le, lattice.le_infi_iff] at this,
  exact this,
  { intros, apply B_ext_left_realize_bounded_formula },
  { intros, apply B_ext_right_realize_bounded_formula },
end

-- axiom of union
-- ∀ u x, x ∈ ⋃ u ↔ ∃ y ∈ u, x ∈ y
def axiom_of_union : sentence L_ZFC :=
∀' ∀' (&'0 ∈' ⋃' &'1 ⇔ (∃' (&'0 ∈' &'2 ⊓ &'1 ∈' &'0)))

lemma bSet_models_union : ⊤ ⊩[V β] axiom_of_union :=
begin
  simp [-top_le_iff, forced_in, axiom_of_union, -lattice.le_inf_iff],
  intros x z,
  have := @bv_union_spec' _ _ x ⊤,
  replace this := this z, dsimp at this,
  bv_split, bv_split_goal
end

-- axiom of powerset
-- ∀ u x, x ∈ P(u) ↔ ∀ y ∈ x, y ∈ u

def axiom_of_powerset : sentence L_ZFC :=
  ∀' ∀' (&'0 ∈' P' &'1 ⇔ (∀' (&'0 ∈' &'1 ⟹ &'0 ∈' &'2)))

lemma bSet_models_powerset : ⊤ ⊩[V β] axiom_of_powerset :=
begin
  simp [forced_in, axiom_of_powerset, -lattice.le_inf_iff, -top_le_iff],
  intros x z, have := @bv_powerset_spec _ _ x z,
  rw [subset_unfold'] at this,
  apply le_inf, bv_imp_intro, exact this.mpr H, bv_imp_intro, exact this.mp H
end

/-- &1 ⊆ &0 ↔ ∀ z, (z ∈ &1 ⟹ z ∈ &0)-/
def subset'' {n} (t₁ t₂ : bounded_term L_ZFC n): bounded_formula L_ZFC n :=
∀' (&'0 ∈' (t₁ ↑ 1) ⟹ &'0 ∈' (t₂ ↑ 1))

local infix ` ⊆'`:100 := subset''

@[simp] lemma boolean_realize_bounded_formula_subset {n} {v : dvector (V β) n}
  (t₁ t₂ : bounded_term L_ZFC n) :
  boolean_realize_bounded_formula v (t₁ ⊆' t₂) ([]) =
  boolean_realize_bounded_term v t₁ ([]) ⊆ᴮ boolean_realize_bounded_term v t₂ ([]) :=
by { simp [subset'', subset_unfold'] }

/- `z` is transitive if `∀ x, x ∈ z ⟹ x ⊆ z` -/
def is_transitive_f : bounded_formula L_ZFC 1 := ∀' ((&'0 ∈' &'1) ⟹ &'0 ⊆' &'1)

/- `z` is `∈`-trichotomous if `∀ x y ∈ z, x = y ∨ x ∈ y ∨ y ∈ x` -/
def epsilon_trichotomy_f : bounded_formula L_ZFC 1 :=
∀' ((&'0 ∈' &'1) ⟹''(∀' (&'0 ∈' &'2 ⟹'' (&'1 ≃ &'0 ⊔' &'1 ∈' &'0) ⊔' &'0 ∈' &'1)))

/- `z` is `∈`-well-founded if `∀ x, x ⊆ z ⟹ x ≠ ∅ ⟹ ∃y ∈ x. ∀w ∈ x. w ∉ y`.
  Note: this is true for every set by regularity, so we don't have to assume this. But we do it for
  completeness, to explicitly state that the order relation is well-founded. -/
def epsilon_well_founded_f : bounded_formula L_ZFC 1 :=
∀' (((&'0 ⊆' &'1) ⟹'' ((∼(&'0 ≃ ∅')) ⟹'' ∃' (&'0 ∈' &'1 ⊓' (∀' (&'0 ∈' &'2 ⟹'' ∼(&'0 ∈' &'1)))))))

/- `z` is `∈`-well-order if it is `∈`-well-founded and `∈`-trichotomous. -/
def ewo_f : bounded_formula L_ZFC 1 := epsilon_trichotomy_f ⊓' epsilon_well_founded_f

/- `z` is an ordinal if forms is an `∈`-well-order and `∈` is transitive on `z`. -/
def Ord_f : bounded_formula L_ZFC 1 := ewo_f ⊓' is_transitive_f

@[simp]lemma Ord_f_is_Ord {x : V β} : boolean_realize_bounded_formula (by exact [x]) Ord_f dvector.nil = Ord x :=
by {simp [Ord_f,ewo_f,is_transitive_f,epsilon_well_founded_f, epsilon_trichotomy_f], refl}

-- this is the usual axiom of infinity, plus a characterization of omega as the least limit ordinal
def axiom_of_infinity : sentence L_ZFC :=
  (∅' ∈' ω' ⊓' ∀'(&'0 ∈' ω' ⟹ ∃' (&'0 ∈' ω' ⊓' &'1 ∈' &'0)))
  ⊓' (∃' (Ord_f ⊓' ω' ≃ &'0))
  ⊓' ∀' (Ord_f ⟹ ((∅' ∈' &'0 ⊓' ∀'(&'0 ∈' &'1 ⟹ ∃' (&'0 ∈' &'2 ⊓' &'1 ∈' &'0))) ⟹ ω' ⊆' &0))

lemma bSet_models_infinity : ⊤ ⊩[V β] axiom_of_infinity :=
begin
  simp [forced_in, axiom_of_infinity, boolean_realize_sentence,
    -lattice.le_inf_iff, -top_le_iff],
  refine le_inf _ _,
    { exact bSet_axiom_of_infinity' },
    { refine le_inf _ _,
      { apply bv_use bSet.omega, exact le_inf Ord_omega bv_refl },
      { exact omega_least_is_limit } }
end

-- axiom of regularity
-- ∀ x, x ≠ ∅ ⟹ ∃ y ∈ x, ∀ z ∈ x, z ∉ y

def axiom_of_regularity : sentence L_ZFC :=
  ∀' (∼(&0 ≃ ∅') ⟹ (∃' (&'0 ∈' &'1 ⊓ ∀' (&'0 ∈' &'2 ⟹ ∼(&'0 ∈' &'1)))))

lemma bSet_models_regularity : ⊤ ⊩[V β] axiom_of_regularity :=
begin
  change ⊤ ≤ _, unfold axiom_of_regularity,
  simp[-top_le_iff], intro x,
  bv_imp_intro,
  apply bSet_axiom_of_regularity, convert H
end

/- ∀ x, x ≠ ∅ ∧ ((∀ y, y ⊆ x ∧ ∀ w₁ w₂ ∈ y, w₁ ⊆ w₂ ∨ w₂ ⊆ w₁) → (⋃y) ∈ x)
      → ∃ c ∈ x, ∀ z ∈ x, c ⊆ z → c = z -/
def zorns_lemma : sentence L_ZFC :=
∀' (∼ (&'0 ≃ ∅')
  ⟹ (∀' (&'0 ⊆' &'1 ⊓' (∀' ∀' ((&'1 ∈' &'2 ⊓' &'0 ∈' &'2) ⟹ (&'1 ⊆' &'0 ⊔' &'0 ⊆' &'1)))
    ⟹ (⋃' &' 0 ∈' &'1)))
    ⟹  (∃' (&'0 ∈' &'1 ⊓ ∀' (&'0 ∈' &'2 ⟹ &'1 ⊆' &'0 ⟹ &'1 ≃ &'0 ))))

lemma bSet_models_Zorn : ⊤ ⊩[V β] zorns_lemma :=
begin
  simp [forced_in, zorns_lemma, boolean_realize_sentence, -lattice.le_inf_iff, -top_le_iff, -lattice.le_infi_iff],
  from bSet_zorns_lemma'
end

def ZFC : Theory L_ZFC :=
  {axiom_of_emptyset, axiom_of_ordered_pairs, axiom_of_extensionality, axiom_of_union,
   axiom_of_powerset, axiom_of_infinity, axiom_of_regularity, zorns_lemma} ∪
  set.Union (λ(n : ℕ), axiom_of_collection '' (set.univ : set $ bounded_formula L_ZFC (n+2)))

theorem bSet_models_ZFC : ⊤ ⊩[V β] ZFC :=
begin
  change ⊤ ≤ _, bv_intro f, bv_intro H,
  repeat{auto_cases}; try{subst H}; try {cases H},
  from bSet_models_Zorn _,
  from bSet_models_regularity _,
  from bSet_models_infinity _,
  from bSet_models_powerset _,
  from bSet_models_union _,
  from bSet_models_extensionality _,
  from bSet_models_ordered_pairs _,
  from bSet_models_emptyset _,
  from bSet_models_collection _ ‹_›
end

include β
theorem ZFC_consistent : is_consistent ZFC := consis_of_exists_bmodel (bSet_models_ZFC β)
omit β

/-- f is =ᴮ-extensional if for every w₁ w₂ v₁ v₂, if pair (w₁, v₁) and pair (w₂, v₂) ∈ f and
    w₁ =ᴮ w₂, then v₁ =ᴮ v₂ -/
def is_func_f : bounded_formula L_ZFC 1 :=
∀' ∀' ∀' ∀' ((pair' &'3 &'1 ∈' &'4 ⊓' pair' &'2 &'0 ∈' &'4
  ⟹ (&'3 ≃ &'2 ⟹ &'1 ≃ &'0)))

@[simp]lemma realize_is_func_f {f : V β} : boolean_realize_bounded_formula (by exact [f]) is_func_f dvector.nil = is_func f :=
begin
  simp[is_func_f, bSet.is_func], refl
end

def is_total'_f : bounded_formula L_ZFC 3 :=
(∀' (&'0 ∈' &'3 ⟹ (∃' (&'0 ∈' &'3 ⊓' (pair' &'1 &'0 ∈' &'2)))))

@[simp]lemma realize_is_total'_f {x y f : V β} : boolean_realize_bounded_formula (by exact [f, y, x]) is_total'_f dvector.nil = is_total x y f :=
begin
  simp [bSet.is_total, is_total'_f]
end

-- is_total'_f₂ S y f is the same as is_total'_f y S f
def is_total'_f₂ : bounded_formula L_ZFC 3 :=
(∀' (&'0 ∈' &'2 ⟹ (∃' (&'0 ∈' &'4 ⊓' (pair' &'1 &'0 ∈' &'2)))))

@[simp]lemma realize_is_total'_f₂ {x y f : V β} : boolean_realize_bounded_formula (by exact [f, y, x]) is_total'_f₂ dvector.nil = is_total y x f :=
begin
  rw [bSet.is_total, is_total'_f₂], simp, refl
end

def is_func'_f : bounded_formula L_ZFC 3 :=
  (is_func_f.cast (dec_trivial)) ⊓' is_total'_f

def is_func'_f₂ : bounded_formula L_ZFC 3 :=
(is_func_f.cast dec_trivial) ⊓' is_total'_f₂

@[simp]lemma realize_is_func'_f {x y f : V β} : boolean_realize_bounded_formula (by exact [f, y, x]) is_func'_f dvector.nil = is_func' x y f :=
by simp [is_func'_f, is_func']

@[simp]lemma realize_is_func'_f₂ {x y f : V β} : boolean_realize_bounded_formula (by exact [f, y, x]) is_func'_f₂ dvector.nil = is_func' y x f :=
by simp [is_func'_f₂, is_func']

/-
  `at_most_f x y` means
  `∃ S, ∃ f, S ⊆ y ∧ f contains a function from S to x ∧ f surjects S onto x`
  In `bSet` it corresponds to the formula `larger_than y x`.

  `at_most_f x y` is equivalent to `¬ y ≺ x`.
-/
def at_most_f : bounded_formula L_ZFC 2 :=
∃' (∃' (((&'1 ⊆' &'3) ⊓' (is_func'_f₂).cast (dec_trivial : 3 ≤ 4)) ⊓'
        ∀' ( &0 ∈' &3 ⟹ (∃' (&'0 ∈' &'3 ⊓' pair' &'0 &'1 ∈' &'2)))))

@[simp]lemma realize_at_most_f {x y : V β} :
  boolean_realize_bounded_formula ([y,x]) at_most_f dvector.nil = larger_than x y :=
by simp[larger_than, at_most_f, is_func]


def is_inj_f : bounded_formula L_ZFC 1 :=
∀' ∀' ∀' ∀' (((pair' &'3 &'1 ∈' &'4 ⊓' pair' &'2 &'0 ∈' &'4) ⊓ &'1 ≃ &'0) ⟹ &'3 ≃ &'2)

@[simp]lemma realize_is_inj_f (f : V β) :
  boolean_realize_bounded_formula (by exact [f]) is_inj_f dvector.nil = is_inj f :=
by {simp[is_inj_f, is_inj], refl}

def injects_into_f : bounded_formula L_ZFC 2 :=
 ∃' (is_func'_f ⊓' is_inj_f.cast (dec_trivial))

@[simp]lemma realize_injects_into {x y : V β} :
  boolean_realize_bounded_formula (by exact [y,x]) injects_into_f dvector.nil = injects_into x y :=
by {simp[injects_into_f, injects_into]}

def non_empty_f : bounded_formula L_ZFC 1 := ∼(&'0 ≃ ∅')

@[simp]lemma non_empty_f_is_non_empty {x : V β} : boolean_realize_bounded_formula (by exact [x]) non_empty_f dvector.nil = not_empty x := by {simp[non_empty_f], refl}

/-- The continuum hypothesis is given by the formula
  `∀x, x is an ordinal ⟹ x ≤ ω ∨ P(ω) ≤ x`.
  Here `a ≤ b` means there is a surjection from a subset of `b` to `a`.
  We have to perform two substitutions (`substmax_bounded_formula` and `[../0]`)
  to apply `at_most_f` to the appropriate arguments. -/
def CH_f : sentence L_ZFC :=
∀' (Ord_f ⟹ (substmax_bounded_formula at_most_f ω' ⊔' at_most_f[Powerset omega/0]))

variable {β}
lemma CH_f_is_CH : ⟦CH_f⟧[V β] = CH₂ :=
begin
  have h1 : ∀(x : V β), boolean_realize_bounded_formula ([x])
    (substmax_bounded_formula at_most_f omega) ([]) =
    boolean_realize_bounded_formula ([x,omega]) at_most_f ([]),
  { intro, refl },
  have h2 : ∀(x : V β), boolean_realize_bounded_formula ([x]) (at_most_f[P' omega /0]) ([]) =
    boolean_realize_bounded_formula (([bv_powerset omega, x] : dvector (V β) 2)) at_most_f ([]),
  { intro, refl },
  -- note: once we have proven realize_substmax_bf and realize_subst0_bf, we can add them to this simp set
  simp [-substmax_bounded_formula, CH_f, CH₂, neg_supr, sup_assoc, h1, h2, lattice.imp]
end

lemma CH_f_sound {Γ : β} : Γ ⊩[V β] CH_f ↔ Γ ≤ CH₂ :=
by {change _ ≤ _ ↔ _ ≤ _, rw CH_f_is_CH}

lemma neg_CH_f_sound {Γ : β} : Γ ⊩[V β] ∼CH_f ↔ Γ ≤ - CH₂ :=
by {change _ ≤ _ ↔ _ ≤ _, rw [boolean_realize_sentence_not, CH_f_is_CH]}

end ZFC

open pSet cardinal

section CH_unprovable


lemma V_𝔹_cohen_models_neg_CH : ⊤ ⊩[V 𝔹_cohen] ∼CH_f :=
begin
  rw neg_CH_f_sound, exact neg_CH₂
end

instance V_𝔹_nonempty : nonempty (V 𝔹_cohen) := ⟨bSet.empty⟩

theorem CH_f_unprovable : ¬ (ZFC ⊢' CH_f) :=
unprovable_of_model_neg _ (bSet_models_ZFC _) (nontrivial.bot_lt_top) V_𝔹_cohen_models_neg_CH

end CH_unprovable

open collapse_algebra

section neg_CH_unprovable

instance V_𝔹_collapse_nonempty : nonempty (V 𝔹_collapse) := ⟨bSet.empty⟩

lemma V_𝔹_collapse_models_CH : ⊤ ⊩[V 𝔹_collapse] CH_f :=
by { rw CH_f_sound, exact CH₂_true }

theorem neg_CH_f_unprovable : ¬ (ZFC ⊢' ∼CH_f) :=
unprovable_of_model_neg (V 𝔹_collapse) (bSet_models_ZFC _)
  (nontrivial.bot_lt_top) (by {rw forced_in_not, from V_𝔹_collapse_models_CH})

end neg_CH_unprovable

section
-- a nicer formulation of CH using formulae

@[simp] def Powerset_t : term L_ZFC → term L_ZFC := app (func ZFC_func.P)
@[simp] def omega_t : term L_ZFC := func ZFC_func.ω
@[simp] def leq_f : formula L_ZFC := at_most_f.fst
@[simp] def is_ordinal : formula L_ZFC := Ord_f.fst

def CH_formula : formula L_ZFC :=
∀' (is_ordinal ⟹ leq_f[omega_t//1] ⊔ leq_f[Powerset_t omega_t//0])

lemma CH_f_fst : CH_f.fst = CH_formula :=
by { simp [CH_f, CH_formula, -substmax_bounded_formula], refl }

end
