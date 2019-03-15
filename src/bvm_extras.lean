import .bvm

open lattice

universe u

local infix ` ⟹ `:65 := lattice.imp

local infix ` ⇔ `:50 := lattice.biimp

namespace bSet
variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]
section extras
@[reducible]def pair (x y : bSet 𝔹) : bSet 𝔹 := {{x}, {x,y}}

-- lemma pair_type (x y : bSet 𝔹) : (pair x y).type = begin end := sorry

--TODO(jesse) write a tactic to automate this type of argument
@[simp]lemma subst_congr_pair_left {x z y : bSet 𝔹} : x =ᴮ z ≤ pair x y =ᴮ pair z y :=
begin
  unfold pair, have this₁ : x =ᴮ z ≤ {{x},{x,y}} =ᴮ {{z},{x,y}} := by simp*,
  have this₂ : x =ᴮ z ≤ {{z},{x,y}} =ᴮ {{z},{z,y}} := by simp*,
  apply bv_context_trans; from ‹_›
end

@[simp, cleanup]lemma insert1_bval_none {u v : bSet 𝔹} : (bSet.insert1 u ({v})).bval none  = ⊤ :=
by refl

@[simp, cleanup]lemma insert1_bval_some {u v : bSet 𝔹} {i} : (bSet.insert1 u {v}).bval (some i) = (bval {v}) i :=
by refl

@[simp, cleanup]lemma insert1_func_none {u v : bSet 𝔹} : (bSet.insert1 u ({v})).func none  = u :=
by refl

@[simp, cleanup]lemma insert1_func_some {u v : bSet 𝔹} {i} : (bSet.insert1 u ({v})).func (some i) = (func {v}) i :=
by refl

@[simp]lemma mem_singleton {x : bSet 𝔹} : ⊤ ≤ x ∈ᴮ {x} :=
by {rw[mem_unfold], apply bv_use none, unfold singleton, simp}

lemma eq_of_mem_singleton' {x y : bSet 𝔹} : y ∈ᴮ {x} ≤ x =ᴮ y :=
by {rw[mem_unfold], apply bv_Or_elim, intro i, cases i, simp[bv_eq_symm], repeat{cases i}}

lemma eq_of_mem_singleton {x y : bSet 𝔹} {c : 𝔹} {h : c ≤ y ∈ᴮ {x}} : c ≤ x =ᴮ y :=
le_trans h (by apply eq_of_mem_singleton')

lemma eq_inserted_of_eq_singleton {x y z : bSet 𝔹} : {x} =ᴮ bSet.insert1 y {z} ≤ x =ᴮ y :=
begin
  rw[bv_eq_unfold], apply bv_specialize_left none, apply bv_specialize_right none,
  unfold singleton, simp, rw[inf_sup_right], apply bv_or_elim,
  apply inf_le_left, apply inf_le_right_of_le, simp[eq_of_mem_singleton']
end

lemma insert1_symm (y z : bSet 𝔹) : ⊤ ≤ bSet.insert1 y {z} =ᴮ bSet.insert1 z {y} :=
begin
  rw[bv_eq_unfold], apply le_inf; bv_intro i; simp; cases i; simp[-top_le_iff],
  {simp[bv_or_right]},
  {cases i; [simp, repeat{cases i}]},
  {simp[bv_or_right]},
  {cases i; [simp, repeat{cases i}]}
end

lemma eq_inserted_of_eq_singleton' {x y z : bSet 𝔹} : {x} =ᴮ bSet.insert1 y {z} ≤ x =ᴮ z :=
by {apply bv_have_true (insert1_symm y z), apply le_trans, apply bv_eq_trans, apply eq_inserted_of_eq_singleton}

example {y z : bSet 𝔹} : ⊤ ≤ ({y,z} : bSet 𝔹) =ᴮ ({z,y}) := insert1_symm _ _

lemma eq_of_eq_pair'_left {x z y : bSet 𝔹} : pair x y =ᴮ pair z y ≤ x =ᴮ z :=
begin
  unfold pair, unfold has_insert.insert, rw[bv_eq_unfold], fapply bv_specialize_left,
  exact some none, fapply bv_specialize_right, exact some none, simp,
  rw[inf_sup_right_left_eq], repeat{apply bv_or_elim},
  {apply le_trans, apply inf_le_inf; apply eq_inserted_of_eq_singleton, {[smt] eblast_using[bv_eq_symm, bv_eq_trans]}},
  {apply inf_le_right_of_le, apply le_trans, apply eq_of_mem_singleton', apply eq_of_eq_singleton, refl},
  {apply inf_le_left_of_le, apply le_trans, apply eq_of_mem_singleton', apply eq_of_eq_singleton, rw[bv_eq_symm]},
  {apply inf_le_left_of_le, apply le_trans, apply eq_of_mem_singleton', apply eq_of_eq_singleton, rw[bv_eq_symm]}
end

lemma inserted_eq_of_insert_eq {y v w : bSet 𝔹} : {v,y} =ᴮ {v,w} ≤ y =ᴮ w :=
begin
  unfold has_insert.insert, rw[bv_eq_unfold], apply bv_specialize_left none,
  apply bv_specialize_right none, change (⊤ ⟹ _) ⊓ (⊤ ⟹ _ : 𝔹) ≤ _, simp,
  rw[inf_sup_right_left_eq], repeat{apply bv_or_elim},
  apply inf_le_left, apply inf_le_left, apply inf_le_right_of_le, rw[bv_eq_symm],
  apply le_trans, apply inf_le_inf; apply eq_of_mem_singleton',
  {[smt] eblast_using[bv_eq_symm, bv_eq_trans]}
end

lemma eq_of_eq_pair'_right {x z y : bSet 𝔹} : pair y x =ᴮ pair y z ≤ x =ᴮ z :=
begin
  unfold pair has_insert.insert, rw[bv_eq_unfold], apply bv_specialize_left none,
  apply bv_specialize_right none, unfold singleton, simp, rw[inf_sup_right_left_eq],
  repeat{apply bv_or_elim},
    {apply inf_le_left_of_le, apply inserted_eq_of_insert_eq},
    {apply inf_le_left_of_le, apply inserted_eq_of_insert_eq},
    {apply inf_le_right_of_le, rw[bv_eq_symm], apply inserted_eq_of_insert_eq},
    {apply le_trans, apply inf_le_inf; apply eq_of_mem_singleton',
     apply le_trans, apply inf_le_inf; apply eq_inserted_of_eq_singleton, rw[bv_eq_symm], apply bv_eq_trans} 
end

section distribution
run_cmd mk_simp_attr `dnf

@[dnf]lemma distrib_inf_over_sup_from_left {β : Type*} [distrib_lattice β] {a b c : β} :
  c ⊓ (a ⊔ b) = (c ⊓ a) ⊔ (c ⊓ b) := by apply inf_sup_left

@[dnf]lemma distrib_inf_over_sup_from_right {β : Type*} [distrib_lattice β] {a b c : β} :
  (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c) := by apply inf_sup_right

end distribution
/- Taken together, eq_of_eq_pair_left and eq_of_eq_pair_right say that x = v and y = w if and only if pair x y = pair v w -/
theorem eq_of_eq_pair_left {x y v w: bSet 𝔹} : pair x y =ᴮ pair v w ≤ x =ᴮ v :=
begin
  unfold pair has_insert.insert, rw[bv_eq_unfold], apply bv_specialize_left none, apply bv_specialize_right (some none),
  unfold singleton, simp, simp only with dnf, repeat{apply bv_or_elim},
  {apply inf_le_right_of_le, apply le_trans, apply eq_inserted_of_eq_singleton', rw[bv_eq_symm]},
  {apply inf_le_left_of_le, rw[mem_unfold], apply bv_Or_elim, intro i, cases i,
   apply inf_le_right_of_le, simp, rw[bv_eq_symm], apply le_trans, apply eq_inserted_of_eq_singleton', rw[bv_eq_symm],
   repeat{cases i}},
  {apply inf_le_right_of_le, apply le_trans, fapply eq_of_mem_singleton, from {x}, from {v},
   refl, apply eq_of_eq_singleton, refl},
  {apply inf_le_right_of_le, apply le_trans, fapply eq_of_mem_singleton, from {x}, from {v},
   refl, apply eq_of_eq_singleton, refl}
end

theorem eq_of_eq_pair_right {x y v w: bSet 𝔹} : pair x y =ᴮ pair v w ≤ y =ᴮ w :=
begin
  apply bv_have, apply eq_of_eq_pair_left,
  apply le_trans, show 𝔹, from pair v y =ᴮ pair v w,
  rw[inf_comm], apply le_trans, apply inf_le_inf, swap, refl,
  apply subst_congr_pair_left, exact y, rw[bv_eq_symm],
  apply bv_eq_trans, apply eq_of_eq_pair'_right
end

@[reducible]def prod (v w : bSet 𝔹) : bSet 𝔹 := ⟨v.type × w.type, λ a, pair (v.func a.1) (w.func a.2), λ a, (v.bval a.1) ⊓ (w.bval a.2)⟩

@[simp, cleanup]lemma prod_type {v w : bSet 𝔹} : (prod v w).type = (v.type × w.type) := by refl

@[simp, cleanup]lemma prod_bval {v w : bSet 𝔹} {a b} : (prod v w).bval (a,b) = v.bval a ⊓ w.bval b := by refl

@[simp, cleanup]lemma prod_type_forall {v w : bSet 𝔹} {ϕ : (prod v w).type → 𝔹} :
  (⨅(z:(prod v w).type), ϕ z) = ⨅(z : v.type × w.type), ϕ z :=
by refl

@[simp]lemma prod_mem {v w x y : bSet 𝔹} : x ∈ᴮ v ⊓ y ∈ᴮ w ≤ pair x y ∈ᴮ prod v w :=
begin
  simp[pair, prod], simp only[mem_unfold], apply bv_cases_left, intro i,
  apply bv_cases_right, intro j, apply bv_use (i,j), tidy,
    {rw[inf_assoc], apply inf_le_left},
    {rw[inf_comm], simp [inf_assoc]},
    {let a := _, let b := _, change (bval v i ⊓ a) ⊓ (bval w j ⊓ b) ≤ _,
     have : a ⊓ b ≤ {{x}, {x, y}} =ᴮ {{func v i}, {x,y}}, by simp*,
     have : a ⊓ b ≤ {{func v i}, {x,y}} =ᴮ {{func v i}, {func v i, func w j}},
       by {apply subst_congr_insert1_left'', have this₁ : a ⊓ b ≤ {x,y} =ᴮ {func v i, y}, by simp*,
       have this₂ : a ⊓ b ≤ {func v i, y} =ᴮ {func v i, func w j}, by simp*,
       apply bv_context_trans; from ‹_›},
    
     apply le_trans, show 𝔹, from a ⊓ b,
       by {ac_change (bval v i ⊓ bval w j) ⊓ (a ⊓ b) ≤ a ⊓ b, apply inf_le_right},
     apply bv_context_trans; from ‹_›}
end


-- /-- f is =ᴮ-extensional on x if for every w₁ and w₂ ∈ x, if w₁ =ᴮ w₂, then for every v₁ and v₂, if (w₁,v₁) ∈ f and (w₂,v₂) ∈ f, then v₁ =ᴮ v₂ -/
-- @[reducible]def is_extensional (x f : bSet 𝔹) : 𝔹 :=
-- ⨅w₁, w₁ ∈ᴮ x ⟹ (⨅w₂, w₂ ∈ᴮ x ⟹ (w₁ =ᴮ w₂ ⟹ ⨅v₁ v₂, (pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f) ⟹ v₁ =ᴮ v₂))

/-- f is =ᴮ-extensional if for every w₁ w₂ v₁ v₂, if pair (w₁ v₁) and pair (w₂ v₂) ∈ f and
    w₁ =ᴮ w₂, then v₁ =ᴮ v₂ -/
@[reducible]def is_extensional (f : bSet 𝔹) : 𝔹 :=
  ⨅ w₁, ⨅w₂, ⨅v₁, ⨅ v₂, pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⟹ (w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂)

/-- f is a functional relation if for every z ∈ x, if there exists a w ∈ y such that (z,w) ∈ f, then for every w' ∈ y such that (z,w') ∈ f, w' =ᴮ w -/
-- @[reducible] def is_functional (x y f : bSet 𝔹) : 𝔹 :=
-- ⨅z, (z∈ᴮ x ⟹ (⨆w, w ∈ᴮ y ⊓ pair z w ∈ᴮ f ⊓ (⨅w', w' ∈ᴮ y ⟹ (pair z w' ∈ᴮ f ⟹ w =ᴮ w'))))

@[reducible]def is_functional (f : bSet 𝔹) : 𝔹 :=
⨅z, (⨆w, pair z w ∈ᴮ f) ⟹ (⨆w', ⨅w'', pair z w'' ∈ᴮ f ⟹ w' =ᴮ w'')
  
-- f is a function if it is a subset of prod x y and it satisfies the following two conditions:
-- 1. it is =ᴮ-extensional
-- 2. it is a functional relation
def is_func (f : bSet 𝔹) : 𝔹 := (is_extensional f) ⊓ (is_functional f)

/-- f is a function from x to y if it is a subset of prod x y such that for every element of x, there exists an element of y such that the pair is in f, and f is a function -/
def is_func' (x y f : bSet 𝔹) : 𝔹 :=
  is_func f ⊓ f ⊆ᴮ prod x y ⊓ ⨅w₁, w₁ ∈ᴮ x ⟹ ⨆w₂, pair x w₂ ∈ᴮ f

/-- f is an injective function on x if it is a function and for every w₁ and w₂ ∈ x, if there exist v₁ and v₂ such that (w₁, v₁) ∈ f and (w₂, v₂) ∈ f,
  then v₁ = v₂ implies  w₁ = w₂ -/
-- def is_inj_func (x y) (f : bSet 𝔹) : 𝔹 :=
--   is_func x y f ⊓ (⨅w₁ w₂, w₁ ∈ᴮ x ⊓ w₂ ∈ᴮ x ⟹
--     (⨆v₁ v₂, (pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⊓ v₁ =ᴮ v₂ ⟹ w₁ =ᴮ w₂)))

def is_inj (f : bSet 𝔹) : 𝔹 :=
  ⨅w₁, ⨅ w₂, ⨅v₁, ⨅ v₂, pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⊓ v₁ =ᴮ v₂ ⟹ w₁ =ᴮ w₂

def function.mk {u : bSet 𝔹} (F : u.type → bSet 𝔹) (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) : bSet 𝔹 :=
⟨u.type, λ a, pair (u.func a) (F a), u.bval⟩

@[simp, cleanup]lemma function.mk_type {u : bSet 𝔹} {F : u.type → bSet 𝔹} {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} : (function.mk F h_congr).type = u.type := by refl

@[simp, cleanup]lemma function.mk_func {u : bSet 𝔹} {F : u.type → bSet 𝔹} {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} {i} : (function.mk F h_congr).func i = pair(u.func i) (F i) := by refl

@[simp, cleanup]lemma function.mk_bval {u : bSet 𝔹} {F : u.type → bSet 𝔹} {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} {i} : (function.mk F h_congr).bval i = u.bval i := by refl

@[simp]lemma function.mk_self {u : bSet 𝔹} {F : u.type → bSet 𝔹} {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} {i : u.type} : u.bval i ≤ pair (u.func i) (F i) ∈ᴮ function.mk F h_congr :=
by {rw[mem_unfold], apply bv_use i, simp}

@[simp]lemma function.mk_self' {u : bSet 𝔹} {F : u.type → bSet 𝔹} {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j}  {i : u.type} : ⊤ ≤ u.bval i ⟹ pair (u.func i) (F i) ∈ᴮ function.mk F h_congr :=
by simp

/-- This is analogous to the check operation: we collect a type-indexed collection of bSets into a definite bSet -/
def check' {α : Type u} (A : α → bSet 𝔹) : bSet 𝔹 := ⟨α, A, λ x, ⊤⟩

@[simp, cleanup]def check'_type {α : Type u} {A : α → bSet 𝔹} : (check' A).type = α := by refl
@[simp, cleanup]def check'_bval {α : Type u} {A : α → bSet 𝔹} {i} : (check' A).bval i = ⊤ := by refl
@[simp, cleanup]def check'_func {α : Type u} {A : α → bSet 𝔹} {i} : (check' A).func i = A i := by refl

lemma mk_is_func {u : bSet 𝔹} (F : u.type → bSet 𝔹) (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) : ⊤ ≤ is_func (function.mk F h_congr) :=
begin
  apply le_inf, bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂,
  apply bv_imp_intro, apply bv_imp_intro, tidy_context,
  bv_cases_at a_left_right_left i,
  bv_cases_at a_left_right_right j,
  clear a_left_right_left a_left_right_right a_left_left,
  bv_split_at a_left_right_left_1, bv_split_at a_left_right_right_1,
  bv_mp a_left_right_left_1_1_1 eq_of_eq_pair_left,
  bv_mp a_left_right_left_1_1_1 eq_of_eq_pair_right,
  bv_mp a_left_right_right_1_1_1 eq_of_eq_pair_left,
  bv_mp a_left_right_right_1_1_1 eq_of_eq_pair_right,
  change Γ_2 ≤ (λ z, z =ᴮ v₂) _, apply bv_rw' a_left_right_left_1_1_1_2,
  simp, change _ ≤ (λ z, (F i) =ᴮ z) _, apply bv_rw' a_left_right_right_1_1_1_2,
  simp, apply le_trans, swap, apply h_congr,
  apply bv_context_trans, rw[bv_eq_symm], from ‹_›,
  apply bv_context_trans, from ‹_›, from ‹_›,

  bv_intro z, apply bv_imp_intro, rw[top_inf_eq], apply bv_Or_elim, intro w,
  apply bv_use w, bv_intro w'', apply bv_imp_intro, tidy_context,
  bv_cases_at a_left i, bv_cases_at a_right j,
  bv_split_at a_left_1, bv_split_at a_right_1,
  bv_mp a_left_1_1_1 (eq_of_eq_pair_left),   bv_mp a_left_1_1_1 (eq_of_eq_pair_right),
  bv_mp a_right_1_1_1 (eq_of_eq_pair_left),  bv_mp a_right_1_1_1 (eq_of_eq_pair_right),
  have : Γ_2 ≤ F i =ᴮ F j,
    by {apply le_trans, swap, apply h_congr i j, apply bv_context_trans, rw[bv_eq_symm], from ‹_›, from ‹_›},
  apply bv_context_trans, from ‹_›, apply bv_context_trans, from ‹_›, rw[bv_eq_symm], from ‹_›
end

-- lemma mk_is_func {u : bSet 𝔹} (F : u.type → bSet 𝔹) (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) : ⊤ ≤ is_func u (check' F) (function.mk F h_congr) :=
-- begin
-- repeat{apply le_inf},
--   {bv_intro i, apply bv_imp_intro, have := @prod_mem 𝔹 _ u (check' F) (func u i) (F i),
--   apply le_trans _ this, apply le_inf, simp[mem.mk'], apply bv_use i, simp},

--   {bv_intro x, apply bv_imp_intro, bv_intro y, repeat{apply bv_imp_intro},
--    bv_intro v₁, bv_intro v₂, apply bv_imp_intro,
--    /- `tidy_context` says -/ apply poset_yoneda, intros Γ a, simp only [le_inf_iff] at a, cases a, cases a_right, cases a_left, cases a_left_left, cases a_left_left_left,
--    rw[mem_unfold] at a_right_left a_right_right,
--    bv_cases_at a_right_right i, specialize_context Γ,
--    bv_cases_at a_right_left j, specialize_context Γ_1,
--    clear a_right_right a_right_left,
--    bv_split_at a_right_left_1, bv_split_at a_right_right_1,
--    simp only with cleanup at a_right_left_1_1_1 a_right_right_1_1_1,
--    bv_mp a_right_right_1_1_1 (eq_of_eq_pair_left),
--    bv_mp a_right_right_1_1_1 (eq_of_eq_pair_right), -- TODO(jesse) generate sane variable names
--    bv_mp a_right_left_1_1_1 (eq_of_eq_pair_left),
--    bv_mp a_right_left_1_1_1 (eq_of_eq_pair_right),
--    have : Γ_2 ≤ func u i =ᴮ func u j, apply bv_context_trans, rw[bv_eq_symm],
--    assumption, rw[bv_eq_symm], apply bv_context_trans, rw[bv_eq_symm],
--    assumption, assumption, -- TODO(jesse) write a cc-like tactic to automate this
--    suffices : Γ_2 ≤ F i =ᴮ F j,
--     by {apply bv_context_trans, assumption, rw[bv_eq_symm], apply bv_context_trans,
--        assumption, from this},
--    apply le_trans this, apply h_congr}, -- the tactics are a success!
--   {bv_intro z, rw[<-deduction], rw[top_inf_eq], rw[mem_unfold], apply bv_Or_elim,
--    intro i_z, apply bv_use (F i_z), repeat{apply le_inf},
--      {tidy_context, rw[mem_unfold], apply bv_use i_z, apply le_inf, apply le_top, simp},
--      tidy_context, bv_mp a_right (subst_congr_pair_left), show bSet 𝔹, from (F i_z),
--      change Γ ≤ (λ w, w ∈ᴮ function.mk F h_congr) (pair z (F i_z)),
--      apply bv_rw' a_right_1, apply B_ext_mem_left, apply bv_use i_z, apply le_inf ‹_›,
--      simp[bv_eq_refl],
--      bv_intro w', repeat{apply bv_imp_intro}, tidy_context,
--      rw[mem_unfold] at a_left_right, bv_cases_at a_left_right i_w',
--      specialize_context Γ, bv_split_at a_left_right_1,
--      change _ ≤ (λv, (F i_z) =ᴮ v) w', apply bv_rw' a_left_right_1_1_1,
--      {simp[B_ext], intros x y, rw[inf_comm], apply bv_eq_trans},
--      change Γ_1 ≤ F i_z =ᴮ F i_w', simp only with cleanup at *,
--      bv_cases_at a_right i_pair, specialize_context Γ_1, bv_split_at a_right_1,
--      bv_mp a_right_1_1_1 (eq_of_eq_pair_left), bv_mp a_right_1_1_1 (eq_of_eq_pair_right),
--      bv_split_at a_left_right_1, clear a_right_1_1 a_right_1 a_left_right_1_1 a_left_right_1_2 a_right_1_1_1,
--      clear a_left_right_1 a_left_right a_left_left_left a_right,
--      have : Γ_2 ≤ F i_z =ᴮ F i_pair,
--        by {apply le_trans _ (h_congr _ _), apply bv_context_trans, rw[bv_eq_symm], from ‹_›, from ‹_›},
--      apply bv_context_trans, exact this, apply bv_context_trans, rw[bv_eq_symm], from ‹_›, from ‹_›}
-- end

lemma mk_inj_of_inj {u : bSet 𝔹} {F : u.type → bSet 𝔹} (h_inj : ∀ i j, i ≠ j → F i =ᴮ F j ≤ ⊥) (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) :
  ⊤ ≤ is_inj (function.mk F h_congr) :=
begin
  bv_intro w₁, bv_intro w₂, bv_intro v₁, bv_intro v₂, apply bv_imp_intro,
  rw[top_inf_eq], rw[mem_unfold, mem_unfold], rw[deduction],
  apply bv_cases_left, intro i, apply bv_cases_right, intro j, apply bv_imp_intro,
  simp,
  tidy_context,
    haveI : decidable (i = j) := classical.prop_decidable _,
    by_cases i = j,
      {subst h, have : Γ ≤ pair w₁ v₁ =ᴮ pair w₂ v₂, by apply bv_context_trans; {tidy},
       bv_mp this eq_of_eq_pair_left, from ‹_›},
    have := h_inj i j h, by_cases Γ = ⊥, rw[h], apply bot_le,
    suffices : Γ = ⊥, by contradiction,
    apply bot_unique,
    suffices : Γ ≤ F i =ᴮ F j, by {apply le_trans this ‹_›},
    bv_mp a_left_left_right eq_of_eq_pair_right,
    bv_mp a_left_right_right eq_of_eq_pair_right,
    apply bv_context_trans, rw[bv_eq_symm], from ‹_›,
    apply bv_context_trans, from a_right, from ‹_›
end

-- lemma mk_inj_of_inj {u : bSet 𝔹} {F : u.type → bSet 𝔹} (h_inj : ∀ i j, i ≠ j → F i =ᴮ F j ≤ ⊥) (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) :
--   ⊤ ≤ is_inj_func u (check' F) (function.mk F h_congr) :=
-- begin
--   apply le_inf, apply mk_is_func,
--   bv_intro w₁, bv_intro w₂, apply bv_imp_intro, rw[top_inf_eq],
--   rw[mem_unfold, mem_unfold], apply bv_cases_left, intro i,
--   apply bv_cases_right, intro j, apply le_supr_of_le (F i),
--   apply le_supr_of_le (F j), apply bv_imp_intro,
--   tidy_context,
--     haveI : decidable (i = j) := by apply classical.prop_decidable,
--     by_cases i = j,
--       { subst h, apply bv_context_trans, tidy},
--     have := h_inj i j h,
--     by_cases Γ = ⊥, rw[h], apply bot_le,
--     suffices : Γ = ⊥, by contradiction,
--     apply bot_unique, from le_trans ‹_› this
-- end

lemma bot_of_mem_self {x : bSet 𝔹} : ⊤ ≤ (x ∈ᴮ x ⟹ ⊥) :=
begin
  induction x, simp[-imp_bot], intro i, specialize x_ih i,
  apply bot_unique, apply bv_have_true x_ih, tidy_context,
  bv_mp a_left_left (show x_B i ≤ x_A i ∈ᴮ mk x_α x_A x_B, by apply mem.mk),
  change Γ ≤ (x_A i ∈ᴮ mk x_α x_A x_B) at a_left_left_1,
  have : Γ ≤ x_A i ∈ᴮ x_A i, rw[show Γ = Γ ⊓ Γ, by simp],
  apply le_trans, apply inf_le_inf, exact a_left_right, exact a_left_left_1,
  apply subst_congr_mem_right,
  have x_ih2 : Γ ≤ _ := le_trans (le_top) x_ih,
  exact context_imp_elim x_ih2 ‹_›
end

-- lemma bot_of_mem_mem_aux {x : bSet 𝔹} {i : x.type} : ⊤ ≤ ( x ∈ᴮ x.func i ⟹ ⊥) :=
-- begin
--   induction x, apply bv_imp_intro, rw[top_inf_eq], rw[mem_unfold],
--   apply bv_Or_elim, intro j,
--   specialize x_ih i, swap, exact j, tidy_context,
--   bv_mp a_left (show bval (func (mk x_α x_A x_B) i) j ≤ (func (func (mk _ _ _) i) j) ∈ᴮ func (mk _ _ _) i, by apply mem.mk'),
-- end

lemma bot_of_mem_mem (x y : bSet 𝔹) : ⊤ ≤ ((x ∈ᴮ y ⊓ y ∈ᴮ x) ⟹ ⊥) :=
begin
  induction x generalizing y, induction y,
  simp[-imp_bot, -top_le_iff], apply bv_imp_intro, rw[top_inf_eq],
  apply bv_cases_right, intro a', apply bv_cases_left, intro a'',
  specialize x_ih a', tidy_context,
  specialize y_ih a'',
  bv_mp a_right_left (show x_B a' ≤ _ ∈ᴮ (mk x_α x_A x_B), by apply mem.mk),
  change Γ ≤ _ ∈ᴮ (mk x_α x_A x_B) at a_right_left_1,
  bv_mp a_left_left (show y_B a'' ≤ _ ∈ᴮ (mk y_α y_A y_B), by apply mem.mk),
  change Γ ≤ _ ∈ᴮ (mk y_α y_A y_B) at a_left_left_1,
  have this₁ : Γ ≤ x_A a' ∈ᴮ y_A a'', apply le_trans' a_right_left_1,
  apply le_trans, apply inf_le_inf, from a_left_right, refl,
  apply subst_congr_mem_right,
  have this₂ : Γ ≤ y_A a'' ∈ᴮ x_A a', apply le_trans' a_left_left_1,
  apply le_trans, apply inf_le_inf, from a_right_right, refl,
  apply subst_congr_mem_right,
  specialize x_ih (y_A a''), specialize_context_at x_ih Γ,
  bv_to_pi x_ih, apply x_ih, bv_split_goal
end

end extras

section check

lemma check_mem_of_mem {x y : pSet} (h_mem : x ∈ y) : (⊤ : 𝔹) ≤ x̌ ∈ᴮ y̌ :=
begin
  rw[mem_unfold], cases y, unfold has_mem.mem pSet.mem at h_mem,
  cases h_mem with w_y H_w_y, apply bv_use w_y,
  apply le_inf, simp, apply check_top_le_bv_eq ‹_›
end

lemma check_subset_of_subset {x y : pSet} (h_subset : x ⊆ y) : (⊤ : 𝔹) ≤ x̌ ⊆ᴮ y̌ :=
begin
  rw[subset_unfold], cases x, cases y, unfold has_subset.subset pSet.subset at h_subset,
  bv_intro x_j, apply bv_imp_intro, rw[top_inf_eq], apply le_trans, apply mem.mk',
  simp[-top_le_iff], specialize h_subset x_j, cases h_subset with b H_b,
  apply bv_use b, apply check_top_le_bv_eq ‹_›
end

end check

section ordinals
def epsilon_well_orders (x : bSet 𝔹) : 𝔹 :=
(⨅y, y∈ᴮ x ⟹
  (⨅z, z ∈ᴮ x ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y))) ⊓
  (⨅u, u ⊆ᴮ x ⟹ (- (u =ᴮ ∅) ⟹ ⨆y, y∈ᴮ u ⊓ (⨅z', z' ∈ᴮ u ⟹ (- (z' ∈ᴮ y)))))

lemma epsilon_dichotomy (x y z : bSet 𝔹) : epsilon_well_orders x ≤ y ∈ᴮ x ⟹ (z ∈ᴮ x ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y)) :=
begin
  unfold epsilon_well_orders, apply bv_imp_intro, tidy_context,
  bv_to_pi', specialize a_left_left y, dsimp at a_left_left,
  bv_to_pi', specialize a_left_left ‹_›, bv_to_pi', exact a_left_left z
end

def is_transitive (x : bSet 𝔹) : 𝔹 := ⨅y, y∈ᴮ x ⟹ y ⊆ᴮ x

lemma subset_of_mem_transitive {x w : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ is_transitive x) (H₂ : Γ ≤ w ∈ᴮ x) : Γ ≤ w ⊆ᴮ x :=
by {bv_specialize_at H₁ w, bv_to_pi H₁_1, solve_by_elim}

lemma mem_of_mem_subset {w y x : bSet 𝔹} {Γ} (H₁ : Γ ≤ y ⊆ᴮ x) (H₂ : Γ ≤ w ∈ᴮ y) : Γ ≤ w ∈ᴮ x :=
by {rw[subset_unfold'] at H₁, bv_specialize_at H₁ w, bv_to_pi', solve_by_elim}

@[simp] lemma B_ext_is_transitive : B_ext (is_transitive : bSet 𝔹 → 𝔹) :=
by {intros x y, unfold is_transitive, revert x y, change B_ext _, simp}

def Ord (x : bSet 𝔹) : 𝔹 := epsilon_well_orders x ⊓ is_transitive x

/-- x is not larger than y if there does not exist a surjective function from x to y -/
def not_larger_than (x y : bSet 𝔹) : 𝔹 := ⨅f, -(is_func' x y f ⊓ ⨅v, v ∈ᴮ y ⟹ ⨆w, w ∈ᴮ x ⊓ pair w v ∈ᴮ f)

def Card (x : bSet 𝔹) : 𝔹 := Ord(x) ⊓ ⨅y, y ∈ᴮ x ⟹ not_larger_than y x

lemma is_transitive_of_mem_Ord (y x : bSet 𝔹) : Ord x ⊓ y ∈ᴮ x ≤ (is_transitive y) :=
begin
  apply bSet.rec_on' y, clear y, intros y y_ih,

  bv_intro w, apply bv_imp_intro, rw[subset_unfold'], bv_intro z, apply bv_imp_intro, unfold Ord, tidy_context,
  bv_specialize_at a_left_left_left_right y, bv_imp_elim_at a_left_left_left_right_1 ‹_›,
  rw[subset_unfold'] at H, bv_specialize_at H w, bv_imp_elim_at H_1 ‹_›, bv_specialize_at a_left_left_left_right w,
  bv_imp_elim_at a_left_left_left_right_2 ‹_›, rw[subset_unfold'] at H_3,
  bv_specialize_at H_3 z, bv_imp_elim_at H_3_1 ‹_›, bv_mp a_left_left_left_left (epsilon_dichotomy x y z),
  bv_imp_elim_at a_left_left_left_left_1 ‹_›, bv_imp_elim_at H_5 ‹_›, bv_or_elim_at H_6, swap, assumption,
  bv_or_elim_at H_left,
  bv_exfalso, suffices : Γ_2 ≤ y ∈ᴮ w ⊓ w ∈ᴮ y,
    have : Γ_2 ≤ _ := le_trans (le_top) (bot_of_mem_mem y w),
    bv_imp_elim_at this ‹_›, assumption,
  apply le_inf, swap, assumption, apply bv_rw' H_left_1, simp,
  assumption,

  bv_exfalso,
  have a_left_right_old := a_left_right,
  rw[mem_unfold] at a_left_right, bv_cases_at a_left_right i_w, bv_split_at a_left_right_1,
  specialize y_ih i_w, rw[deduction] at y_ih,
  have := le_trans (le_inf ‹_› ‹_› : Γ_3 ≤ Ord x) ‹_›,
  have this' : Γ_3 ≤ func y i_w ∈ᴮ x,  rw[bv_eq_symm] at a_left_right_1_1_1,
  change Γ_3 ≤ (λ z, z ∈ᴮ x) (func y i_w), apply bv_rw' a_left_right_1_1_1,
  simp, from H_2, bv_imp_elim_at this ‹_›,
  have : Γ_3 ≤ is_transitive w, apply bv_rw' ‹_›, simp, from ‹_›,
  unfold is_transitive at this, have H_8 := this z ‹_›,
  rw[subset_unfold'] at H_8, bv_specialize_at H_8 y,
  bv_imp_elim_at H_8_1 ‹_›,
  suffices : Γ_3 ≤ y ∈ᴮ w ⊓ w ∈ᴮ y,
    have this3 := le_trans (@le_top _ _ Γ_3) (bot_of_mem_mem y w),
  bv_to_pi this3, apply this3, bv_split_goal
end

lemma is_ewo_of_mem_Ord (y x : bSet 𝔹) : Ord x ⊓ y ∈ᴮ x ≤ (epsilon_well_orders y) :=
begin
  bv_split_goal, rename i z, apply bv_imp_intro, bv_split_goal; rename i w, apply bv_imp_intro,
  
  all_goals{unfold Ord},
  {unfold epsilon_well_orders, tidy_context,
  bv_to_pi', specialize a_left_left_left_left_left w, dsimp at a_left_left_left_left_left,
  specialize a_left_left_left_right y,
    bv_to_pi a_left_left_left_right, specialize a_left_left_left_right ‹_›,
    rw[subset_unfold'] at a_left_left_left_right, bv_to_pi a_left_left_left_right,
    have H₁ := a_left_left_left_right w, bv_to_pi',
  have H₂ : Γ ≤ w ∈ᴮ x, from H₁ ‹_›,
  have H₃ : Γ ≤ z ∈ᴮ x,
    by {specialize a_left_left_left_right z, bv_to_pi', from a_left_left_left_right ‹_›},
  rename a_left_left_left_left_left H,
  replace H := H ‹_› z ‹_›,
  bv_or_elim_at H, bv_or_elim_at H_left,
  apply le_sup_left_of_le, apply le_sup_left_of_le, bv_split_goal,
  apply le_sup_right_of_le, assumption,
  apply le_sup_left_of_le, apply le_sup_right_of_le, assumption},
  
  
  {repeat{apply bv_imp_intro}, tidy_context,
  rename a_left_left_left_left H, rename i w,
  bv_split, 
 have : Γ ≤ w ⊆ᴮ x,
   by {rw[subset_unfold'], bv_intro w', bv_imp_intro, specialize_context Γ,
       have := mem_of_mem_subset a_left_right H,
       apply mem_of_mem_subset, show bSet 𝔹, from y,
       apply subset_of_mem_transitive ‹_› ‹_›, from ‹_›},
 from H_right w ‹_› ‹_›}
end

theorem Ord_of_mem_Ord (y x : bSet 𝔹) : Ord x ⊓ y ∈ᴮ x ≤ Ord y :=
  le_inf (is_ewo_of_mem_Ord _ _) (is_transitive_of_mem_Ord _ _)

open ordinal
open cardinal

/-- The successor operation on sets (in particular von Neumman ordinals) -/
@[reducible]def succ (x : bSet 𝔹) := bSet.insert1 x x

noncomputable def ordinal.mk : ordinal.{u} → bSet 𝔹 := λ η,
limit_rec_on η ∅ (λ ξ mk_ξ, succ mk_ξ)
begin
intros ξ is_limit_ξ ih,
    let this := ξ.out,
    have H := quotient.out_eq ξ,
    have this' : ξ = @ordinal.type this.α this.r this.wo,
    by { rw[<-H], convert type_def _, dsimp[this], cases ξ.out, refl},
    refine bv_union ⟨this.α, _, λ _, ⊤⟩,
    intro x, apply ih, rw this', apply typein_lt_type, exact x,
end

end ordinals

end bSet
