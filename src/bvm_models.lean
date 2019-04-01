import .bvm .bfol .bvm_extras

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

-- local infix ` ⟹ `:62 := bd_imp

local infix ` ⇔' `:50 := lattice.biimp

-- local infix ` ⇔ `:61 := bd_biimp

section ZFC'
inductive ZFC'_rel : ℕ → Type 1
| ε : ZFC'_rel 2

inductive ZFC'_func : ℕ → Type 1
| emptyset : ZFC'_func 0
| pr : ZFC'_func 2
| ω : ZFC'_func 0
| P : ZFC'_func 1
| Union : ZFC'_func 1

def L_ZFC' : Language.{1} :=
{ functions := ZFC'_func,
  relations := ZFC'_rel }

end ZFC'

variables {𝔹 : Type 0} [nontrivial_complete_boolean_algebra 𝔹]

def bSet_model_fun_map : Π {n : ℕ}, L_ZFC'.functions n → dvector (bSet 𝔹) n → bSet 𝔹 :=
begin
  intros n S,
    induction S,
  from λ _, bSet.empty,
  from λ x, by {cases x, refine bSet.pair x_x _, cases x_xs, from x_xs_x},
  from λ _, bSet.omega,
  from λ x, by {cases x, exact bv_powerset x_x},
  from λ x, by {cases x, from bv_union ‹_›}
end

def bSet_model_rel_map : Π {n : ℕ}, L_ZFC'.relations n → dvector (bSet 𝔹) n → 𝔹 :=
begin
  intros n R, induction R,
  intro x, cases x, cases x_xs,
  from x_x ∈ᴮ x_xs_x
end

variable (𝔹)
def V : bStructure L_ZFC' (𝔹) :=
{ carrier := (bSet 𝔹),
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
        change (_ ⊓ _ : 𝔹) ≤ (bv_powerset _) =ᴮ (bv_powerset _), simp,
        tidy_context, apply bv_powerset_congr ‹_› },
      {intros x y, cases x, cases y, cases x_xs, cases y_xs,
        change (_ ⊓ _ : 𝔹) ≤ (bv_union _) =ᴮ (bv_union _), simp,
        tidy_context, from bv_union_congr ‹_›},
      {intros x y, cases x, cases y, cases x_xs, cases y_xs,
        change (_ ⊓ (_ ⊓ _) : 𝔹) ≤ pair x_x x_xs_x =ᴮ pair y_x y_xs_x,
        cases x_xs_xs, cases y_xs_xs, simp,
        tidy_context, simp[*,pair_congr]}
  end,
  rel_congr :=
  begin
    intros n R, cases R, intros x y,
    cases x, cases y, cases x_xs, cases y_xs,
    cases x_xs_xs, cases y_xs_xs,
    change ((_ ⊓ _) ⊓ (_ ∈ᴮ _) : 𝔹) ≤ (_ ∈ᴮ _), simp,
    tidy_context, apply mem_congr; from ‹_›
  end}

@[simp] lemma carrier_V : ↥(V 𝔹) = bSet 𝔹 := rfl

@[simp]lemma V_forall {C : (V 𝔹) → 𝔹} : (⨅(x : V 𝔹), C x) = (⨅(x : bSet 𝔹), C x) := rfl

@[simp]lemma V_exists {C : (V 𝔹) → 𝔹} : (⨆(x : V 𝔹), C x) = (⨆(x : bSet 𝔹), C x) := rfl

@[simp]lemma V_eq {a b} : (V 𝔹).eq a b = a =ᴮ b := rfl

lemma alpha_equiv₁ {C : (bSet 𝔹) → 𝔹} : (⨅(x : bSet 𝔹), C x) = ⨅(y : bSet 𝔹), C y := rfl
lemma alpha_equiv₂ {C : (bSet 𝔹) → 𝔹} : (⨆(x : bSet 𝔹), C x) = ⨆(y : bSet 𝔹), C y := rfl

def emptyset {n} : bounded_term L_ZFC' n := bd_const ZFC'_func.emptyset

notation `∅'` := emptyset

def omega {n} : bounded_term L_ZFC' n := bd_const ZFC'_func.ω

notation `ω'` := omega

def Powerset {n} : bounded_term L_ZFC' n → bounded_term L_ZFC' n := bd_app (bd_func ZFC'_func.P)

notation `P'` := Powerset

def mem {n} (t₁ t₂ : bounded_term L_ZFC' n) : bounded_formula L_ZFC' n :=
@bounded_formula_of_relation L_ZFC' 2 n ZFC'_rel.ε t₁ t₂

local infix ` ∈'`:100 := _root_.mem

def pair' {n} (t₁ t₂ : bounded_term L_ZFC' n) : bounded_term L_ZFC' n :=
@bounded_term_of_function L_ZFC' 2 n ZFC'_func.pr t₁ t₂

def union' {n} : bounded_term L_ZFC' n → bounded_term L_ZFC' n := bd_app (bd_func ZFC'_func.Union)

notation `⋃'` := union'

local prefix `&'`:max := bd_var


@[simp] lemma boolean_realize_bounded_formula_mem {n} {v : dvector (V 𝔹) n}
  (t₁ t₂ : bounded_term L_ZFC' n) :
  boolean_realize_bounded_formula v (t₁ ∈' t₂) ([]) =
  boolean_realize_bounded_term v t₁ ([]) ∈ᴮ boolean_realize_bounded_term v t₂ ([]) :=
by refl

@[simp] lemma boolean_realize_bounded_term_Union {n} {v : dvector (V 𝔹) n}
  (t : bounded_term L_ZFC' n) :
  boolean_realize_bounded_term v (⋃' t) ([]) =
  bv_union (boolean_realize_bounded_term v t ([])) :=
by refl

@[simp] lemma boolean_realize_bounded_term_Powerset {n} {v : dvector (V 𝔹) n}
  (t : bounded_term L_ZFC' n) :
  boolean_realize_bounded_term v (P' t) ([]) =
  bv_powerset (boolean_realize_bounded_term v t ([])) :=
by refl

@[simp] lemma boolean_realize_bounded_term_omega {n} {v : dvector (V 𝔹) n} :
  boolean_realize_bounded_term v ω' ([]) = bSet.omega :=
by refl

@[simp] lemma boolean_realize_bounded_term_emptyset {n} {v : dvector (V 𝔹) n} :
  boolean_realize_bounded_term v ∅' ([]) = bSet.empty :=
by refl

@[simp]lemma boolean_realize_bounded_term_pair {n} {v : dvector (V 𝔹) n}
  (t₁ t₂ : bounded_term L_ZFC' n) :  boolean_realize_bounded_term v (pair' t₁ t₂) ([]) =
  pair (boolean_realize_bounded_term v t₁ ([])) (boolean_realize_bounded_term v t₂ ([])) :=
by refl

 -- todo do this for pairing

-- @[simp] lemma boolean_realize_bounded_formula_biimp_mem_var {n} {v : dvector (V 𝔹) n}
--   (n₁ n₂ : fin n) :
--   boolean_realize_bounded_formula v (&'n₁ ∈' &'n₂) ([]) =
--   v.nth n₁.1 n₁.2 ∈ᴮ v.nth n₂.1 n₂.2 :=
-- by refl

@[simp] lemma fin_0 {n : ℕ} : (0 : fin (n+1)).1 = 0 := by refl
@[simp] lemma fin_1 {n : ℕ} : (1 : fin (n+2)).1 = 1 := by refl
@[simp] lemma fin_2 {n : ℕ} : (2 : fin (n+3)).1 = 2 := by refl
@[simp] lemma fin_3 {n : ℕ} : (3 : fin (n+4)).1 = 3 := by refl

def axiom_of_emptyset : sentence L_ZFC' := ∀' (∼(&0 ∈' ∅'))

lemma bSet_models_emptyset : ⊤ ⊩[V 𝔹] axiom_of_emptyset :=
by {change ⊤ ≤ _, simp[axiom_of_emptyset, -top_le_iff], intro x, from empty_spec}

def axiom_of_pairing : sentence L_ZFC' :=
 ∀' ∀' ∀' ∀'(((pair' &'3 &'2 ≃pair' &'1 &'0)) ⇔ (&'3 ≃ &'1 ⊓ &'2 ≃ &'0))

lemma bSet_models_pairing : ⊤ ⊩[V 𝔹] axiom_of_pairing :=
begin
  change ⊤ ≤ _, simp[axiom_of_pairing], intros a b x y, tidy,
  from eq_of_eq_pair_left, from eq_of_eq_pair_right,
  simp[pair_congr]
end

-- axiom of extensionality
-- ∀ x y, (∀ z, (z ∈ x ↔ z ∈ y)) → x = y
def axiom_of_extensionality : sentence L_ZFC' :=
∀' ∀' (∀'(&'0  ∈' &'2 ⇔  &'0 ∈' &'1) ⟹ (&1 ≃ &0))

lemma bSet_models_extensionality : ⊤ ⊩[V 𝔹] axiom_of_extensionality :=
by { simp [forced_in, axiom_of_extensionality], exact bSet_axiom_of_extensionality }

-- axiom of collection
-- For every formula ϕ(x,y),
-- ∀ u, (∀ x ∈ u, ∃ y, ϕ(x,y)) ⟹ (∃ v, ∀ z ∈ u, ∃ w ∈ v, ϕ(z,w))

def axiom_of_collection (ϕ' : bounded_formula L_ZFC' 2) : sentence L_ZFC' :=
∀' ((∀' (&'0 ∈' &'1 ⟹ ∃' ϕ'.cast1)) ⟹
(∃' ∀'(&'0 ∈' &'2 ⟹ ∃' (&'0 ∈' &'2 ⊓ ϕ'.cast dec_trivial))))

-- note: should write a lemma which says given the full congr lemma for a 2-ary formula, can extract left and right congr lemmas
lemma bSet_models_collection (ϕ : bounded_formula L_ZFC' 2) : ⊤ ⊩[V 𝔹] axiom_of_collection ϕ :=
begin
  change ⊤ ≤ _, bv_intro u, simp, have := bSet_axiom_of_collection' _ _ _ u,
  simp only [lattice.top_le_iff, bSet.mem, lattice.imp_top_iff_le, lattice.le_infi_iff] at this,
  exact this u,
  { intros,
    let v₁ : ℕ → V 𝔹 := λ n, nat.rec_on n x (λ _ _, z),
    let v₂ : ℕ → V 𝔹 := λ n, nat.rec_on n y (λ _ _, z),
    have h₁ : ∀(k : ℕ) (hk : k < 2), v₁ k = dvector.nth ([x, z]) k hk,
    { intros, cases k, refl, cases k, refl, exfalso, apply not_le_of_gt hk,
      apply nat.succ_le_succ, apply nat.succ_le_succ, apply nat.zero_le },
    have h₂ : ∀(k : ℕ) (hk : k < 2), v₂ k = dvector.nth ([y, z]) k hk,
    { intros, cases k, refl, cases k, refl, exfalso, apply not_le_of_gt hk,
      apply nat.succ_le_succ, apply nat.succ_le_succ, apply nat.zero_le },
    rw [←boolean_realize_bounded_formula_eq h₁, ←boolean_realize_bounded_formula_eq h₂],
    convert boolean_realize_formula_congr _ _ _ _,
    apply le_antisymm, apply le_infi, intro n, cases n,
    refl, simp only [v₁, v₂, bStructure.eq_refl, le_top],
    apply infi_le _ 0 },
  { intros,
    let v₁ : ℕ → V 𝔹 := λ n, nat.rec_on n z (λ _ _, x),
    let v₂ : ℕ → V 𝔹 := λ n, nat.rec_on n z (λ _ _, y),
    have h₁ : ∀(k : ℕ) (hk : k < 2), v₁ k = dvector.nth ([z, x]) k hk,
    { intros, cases k, refl, cases k, refl, exfalso, apply not_le_of_gt hk,
      apply nat.succ_le_succ, apply nat.succ_le_succ, apply nat.zero_le },
    have h₂ : ∀(k : ℕ) (hk : k < 2), v₂ k = dvector.nth ([z, y]) k hk,
    { intros, cases k, refl, cases k, refl, exfalso, apply not_le_of_gt hk,
      apply nat.succ_le_succ, apply nat.succ_le_succ, apply nat.zero_le },
    rw [←boolean_realize_bounded_formula_eq h₁, ←boolean_realize_bounded_formula_eq h₂],
    convert boolean_realize_formula_congr _ _ _ _,
    apply le_antisymm, apply le_infi, intro n, cases n,
    simp only [v₁, v₂, bStructure.eq_refl, le_top], refl,
    apply infi_le _ 1 },
end

-- axiom of union
-- ∀ u x, x ∈ ⋃ u ↔ ∃ y ∈ u, x ∈ y
def axiom_of_union : sentence L_ZFC' :=
∀' ∀' (&'0 ∈' ⋃' &'1 ⇔ (∃' (&'0 ∈' &'2 ⊓ &'1 ∈' &'0)))

lemma bSet_models_union : ⊤ ⊩[V 𝔹] axiom_of_union :=
begin
  simp [-top_le_iff, forced_in, axiom_of_union, -lattice.le_inf_iff],
  intros x z,
  have := @bv_union_spec' _ _ x ⊤,
  replace this := this z, dsimp at this,
  bv_split, bv_split_goal
end

-- axiom of powerset
-- ∀ u x, x ∈ P(x) ↔ ∀ y ∈ x, y ∈ u

def axiom_of_powerset : sentence L_ZFC' :=
  ∀' ∀' (&'0 ∈' P' &'1 ⇔ (∀' (&'0 ∈' &'1 ⟹ &'0 ∈' &'2)))

lemma bSet_models_powerset : ⊤ ⊩[V 𝔹] axiom_of_powerset :=
begin
  simp [forced_in, axiom_of_powerset, -lattice.le_inf_iff, -top_le_iff],
  intros x z, have := @bv_powerset_spec _ _ x z,
  rw [subset_unfold'] at this,
  apply le_inf, bv_imp_intro, exact this.mpr H, bv_imp_intro, exact this.mp H
end

-- axiom of infinity
-- ∅ ∈ ω ∧ ∀ x ∈ ω, ∃ y ∈ ω, x ∈ y

def axiom_of_infinity : sentence L_ZFC' :=
  ∅' ∈' ω' ⊓ ∀'(&'0 ∈' ω' ⟹ ∃' (&'0 ∈' ω' ⊓' &'1 ∈' &'0))

lemma bSet_models_infinity : ⊤ ⊩[V 𝔹] axiom_of_infinity :=
begin
  simp [forced_in, axiom_of_infinity, boolean_realize_sentence, -lattice.le_inf_iff, -top_le_iff],
  exact bSet_axiom_of_infinity'
end

-- axiom of regularity
-- ∀ x, x ≠ ∅ ⟹ ∃ y ∈ x, ∀ z' ∈ x, ¬ (z' ∈ y)

def axiom_of_regularity : sentence L_ZFC' :=
  ∀' (∼(&0 ≃ ∅') ⟹ (∃' (&'0 ∈' &'1 ⊓ ∀' (&'0 ∈' &'2 ⟹ ∼(&'0 ∈' &'1)))))

lemma bSet_models_regularity : ⊤ ⊩[V 𝔹] axiom_of_regularity :=
begin
  change ⊤ ≤ _, unfold axiom_of_regularity,
  simp[-top_le_iff], intro x,
  bv_imp_intro,
  apply bSet_axiom_of_regularity, convert H
end

/-- &1 ⊆ &0 ↔ ∀ z, (z ∈ &1 ⟹ z ∈ &0)-/
def subset'' {n} (t₁ t₂ : bounded_term L_ZFC' n): bounded_formula L_ZFC' n :=
∀' (&'0 ∈' (t₁ ↑ 1) ⟹ &'0 ∈' (t₂ ↑ 1))

local infix ` ⊆'`:100 := subset''

@[simp] lemma boolean_realize_bounded_formula_subset {n} {v : dvector (V 𝔹) n}
  (t₁ t₂ : bounded_term L_ZFC' n) :
  boolean_realize_bounded_formula v (t₁ ⊆' t₂) ([]) =
  boolean_realize_bounded_term v t₁ ([]) ⊆ᴮ boolean_realize_bounded_term v t₂ ([]) :=
by { simp [subset'', subset_unfold'] }

def zorns_lemma : sentence L_ZFC' :=
∀' (∼ (&'0 ≃ ∅')
  ⟹ (∀' (&'0 ⊆' &'1 ⊓' (∀' ∀' ((&'1 ∈' &'2 ⊓' &'0 ∈' &'2) ⟹ (&'1 ⊆' &'0 ⊔' &'0 ⊆' &'1)))
    ⟹ (⋃' &' 0 ∈' &'1)))
    ⟹  (∃' (&'0 ∈' &'1 ⊓ ∀' (&'0 ∈' &'2 ⟹ &'1 ⊆' &'0 ⟹ &'1 ≃ &'0 ))))

lemma bSet_models_Zorn : ⊤ ⊩[V 𝔹] zorns_lemma :=
begin
  simp [forced_in, zorns_lemma, boolean_realize_sentence, -lattice.le_inf_iff, -top_le_iff],
  intro X, bv_imp_intro, bv_imp_intro,
  convert bSet_zorns_lemma' X H H_1
end


-- continuum hypothesis

-- ¬ (∃ z z', ω ≺ z ≺ z' ≼ 𝒫(ω))

-- where ≺ means (¬ larger_than) and ≼ means "exists an injection into"


/-- f is =ᴮ-extensional if for every w₁ w₂ v₁ v₂, if pair (w₁ v₁) and pair (w₂ v₂) ∈ f and
    w₁ =ᴮ w₂, then v₁ =ᴮ v₂ -/
def is_extensional_f : bounded_formula L_ZFC' 1 :=
∀' ∀' ∀' ∀' ((pair' &'3 &'1 ∈' &'4 ⊓' pair' &'2 &'0 ∈' &'4
  ⟹ (&'3 ≃ &'2 ⟹ &'1 ≃ &'0)))

def is_functional_f : bounded_formula L_ZFC' 1 :=
∀' ((∃' (pair' &'1 &'0 ∈' &'2)) ⟹ (∃' ∀' (pair' &'2 &'0 ∈' &'3 ⟹ &'1 ≃ &'0)))

def is_func_f : bounded_formula L_ZFC' 1 :=
  is_extensional_f ⊓' is_functional_f

def is_func'_f : bounded_formula L_ZFC' 3 :=
  is_func_f ⊓' subset' &'0
  -- sorry

def larger_than : bounded_formula L_ZFC' 2 :=
∃' (is_func_f.cast (dec_trivial) ⊓
   ∀' ( &0 ∈' &2 ⟹ (∃' (&'0 ∈' &'4 ⊓' pair' &'0 &'1 ∈' &'2))))

def injects_into : bounded_formula L_ZFC' 2 :=
 ∃' is_func_f

-- c.f. the end of `forcing.lean`

-- where "larger_than" means

-- ∃ f, is_func f ∧ ∀ v ∈ y, ∃ w ∈ x, (w,v) ∈ f

-- also need a definition of the pairing function
-- i.e. define the pairing operation and show it satisfies the axiom
-- ∀ a ∀ b ∃ c ∀ d, (d ∈ c ↔ d = a ∨ d = b)

-- need to characterize 𝒫(ω) and (ω) (powerset is an easy extensionality argument).

-- for ω, need to say that it is a subset of any other ordinal which contains all the natural numbers, which is easy
