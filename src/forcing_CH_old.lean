import .bvm .bvm_extras .regular_open_algebra .to_mathlib data.pfun tactic .pSet_ordinal

/-
  Forcing the continuum hypothesis.
-/

universe u

open lattice bSet topological_space pSet cardinal

local infix ` ⟹ `:65 := lattice.imp

local infix ` ⇔ `:50 := lattice.biimp

local infix `≺`:70 := (λ x y, -(larger_than x y))

local infix `≼`:70 := (λ x y, injects_into x y)

@[reducible]private noncomputable definition ℵ₁ := (card_ex $ aleph 1)

local notation `ω` := (bSet.omega)

local attribute [instance, priority 0] classical.prop_decidable

section lemmas

variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

/-- Corresponds to proposition 5.2 in Moore's 'the method of forcing':
Let x be a set and let ϕ(v) be a formula in the forcing language. If ∀ y ∈ x, p ⊩ ϕ(y̌), then p ⊩ ∀ y ∈ (x̌), ϕ(y)
-/
lemma check_forall (x : pSet) (ϕ : bSet 𝔹 → 𝔹) {h : B_ext ϕ} {b : 𝔹} :
  (∀ (y : x.type), b ≤ ϕ((x.func y)̌ )) → (b ≤ (⨅(y : x.type), ϕ((x.func y)̌ ))) :=
λ H, le_infi ‹_›

lemma aleph_one_check_is_aleph_one_of_omega_lt {Γ : 𝔹} (H : Γ ≤ bSet.omega ≺ (ℵ₁)̌ ): Γ ≤ (ℵ₁̌ ) =ᴮ (aleph_one) :=
begin
  refine subset_ext aleph_one_check_sub_aleph_one _,
  have := @aleph_one_satisfies_Ord_spec _ _ Γ, unfold aleph_one_Ord_spec at this,
  bv_split, revert this_right, bv_split, intro this_right,
  from this_right (ℵ₁ ̌) (by simp) ‹_›
end

theorem CH_true_aux
  (H_aleph_one : ∀{Γ : 𝔹}, Γ ≤ aleph_one_universal_property (ℵ₁̌ ))
  (H_not_lt    : ∀{Γ : 𝔹}, Γ ≤ - ((ℵ₁)̌  ≺ 𝒫(ω)))
  : ∀{Γ : 𝔹}, Γ ≤ CH :=
begin
  intro Γ, unfold CH, rw[<-imp_bot], bv_imp_intro,
  bv_cases_at H x, bv_cases_at H_1 y, clear H H_1, bv_split, bv_split,
  unfold aleph_one_universal_property at H_aleph_one,
  replace H_aleph_one := @H_aleph_one Γ_3 x ‹_›,
  suffices H_aleph_one_lt_continuum : Γ_3 ≤ (ℵ₁)̌  ≺ 𝒫(ω),
    from bv_absurd _ H_aleph_one_lt_continuum H_not_lt,
  from bSet_lt_of_lt_of_le _ y _ (bSet_lt_of_le_of_lt _ x _ ‹_› ‹_›) ‹_›
end

def rel_of_array
  (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
  : bSet 𝔹 :=
set_of_indicator (λ pr, (af pr.1 pr.2) : (prod x y).type → 𝔹)

lemma rel_of_array_surj (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
  (H_bval₁ : ∀ i, x.bval i = ⊤)
  (H_bval₂ : ∀ i, y.bval i = ⊤)
  (H_wide : ∀ j, (⨆ i, af i j) = ⊤) {Γ}
  : Γ ≤ (is_surj x y (rel_of_array x y af)) :=
begin
  bv_intro z, bv_imp_intro Hz, rw[<-@bounded_exists 𝔹 _ x _ _],
  simp [H_bval₁],
    { rw[mem_unfold] at Hz, bv_cases_at Hz i, simp[H_bval₂] at Hz_1,
     apply bv_rw' Hz_1,
       { apply B_ext_supr, intro i,
       from @B_ext_pair_right 𝔹 _ (λ z, z ∈ᴮ rel_of_array x y af) (by simp) _},
       { rw[rel_of_array], simp, rw[supr_comm],
         transitivity ⨆ (j : type x), af j i ⊓
           pair (func x j) (func y i) =ᴮ pair (func x j) (func y i),
        conv {congr, skip, congr, funext, rw[bv_eq_refl _]}, simp[H_wide],
        clear_except, tidy_context,
        bv_cases_at a j, refine bv_use (j,i),
        refine bv_use j, from ‹_›}},
    { change B_ext _, from B_ext_term (B_ext_mem_left) (by simp) }
end

lemma mem_left_of_mem_rel_of_array {x y w₁ w₂ : bSet 𝔹} {af : x.type → y.type → 𝔹}
  {Γ} (H_mem_left : Γ ≤ pair w₁ w₂ ∈ᴮ rel_of_array x y af)
  (H_bval₁ : ∀ i, x.bval i = ⊤)
  : Γ ≤ w₁ ∈ᴮ x :=
begin
  unfold rel_of_array at H_mem_left, dsimp at H_mem_left,
  bv_cases_at H_mem_left p, cases p with i j, dsimp at H_mem_left_1,
  bv_split_at H_mem_left_1, have := eq_of_eq_pair_left' ‹_›,
  apply bv_rw' this, simp, apply mem.mk'', simp only [H_bval₁ _, le_top]
end

lemma mem_right_of_mem_rel_of_array {x y w₁ w₂ : bSet 𝔹} {af : x.type → y.type → 𝔹}
  {Γ} (H_mem_right : Γ ≤ pair w₁ w₂ ∈ᴮ rel_of_array x y af)
  (H_bval₂ : ∀ i, y.bval i = ⊤)
  : Γ ≤ w₂ ∈ᴮ y :=
begin
  unfold rel_of_array at H_mem_right, dsimp at H_mem_right,
  bv_cases_at H_mem_right p, cases p with i j, dsimp at H_mem_right_1,
  bv_split_at H_mem_right_1, have := eq_of_eq_pair_right' ‹_›,
  apply bv_rw' this, simp, apply mem.mk'', simp only [H_bval₂ _, le_top]
end

local attribute [instance] classical.prop_decidable

lemma rel_of_array_extensional (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
  (H_bval₁ : ∀ i, x.bval i = ⊤)
  (H_bval₂ : ∀ i, y.bval i = ⊤)
  (H_wide : ∀ j, (⨆ i, af i j) = ⊤)
  (H_anti : ∀ i, (∀ j₁ j₂, j₁ ≠ j₂ → af i j₁ ⊓ af i j₂ ≤ ⊥))
  (H_inj  : ∀ i₁ i₂, ⊥ < (func x i₁) =ᴮ (func x i₂) → i₁ = i₂)
  {Γ}
  : Γ ≤ (is_func (rel_of_array x y af)) :=
begin
  bv_intro w₁, bv_intro v₁, bv_intro w₂, bv_intro v₂,
  bv_imp_intro H_mem, bv_split,
  bv_imp_intro H_eq,
  have this : Γ_2 ≤ pair w₁ v₂ ∈ᴮ rel_of_array x y af,
    by {apply bv_rw' H_eq,
          { exact B_ext_term (B_ext_mem_left) (by simp) },
          { from ‹_› }},
  clear_except H_mem_left this H_anti H_inj H_eq,
  dsimp[rel_of_array] at H_mem_left this,
  bv_cases_at H_mem_left p₁, cases p₁ with i₁ j₁,
  suffices : Γ_3 ≤ v₂ =ᴮ (y.func j₁),
    by {refine bv_context_trans _ (bv_symm this), bv_split,
         from eq_of_eq_pair_right' ‹_›},
  bv_cases_at this p₂, cases p₂ with i₂ j₂,
  suffices : Γ_4 ≤ (y.func j₂) =ᴮ (func y j₁),
    by {exact bv_context_trans (by bv_split; from eq_of_eq_pair_right' ‹_›) (this)},
  by_cases j₁ = j₂,
    { subst h, from bv_eq_refl'},
    { bv_exfalso, by_cases i₁ = i₂,
        { subst h, specialize H_anti i₁ j₁ j₂ ‹_›, refine le_trans _ H_anti,
          bv_split, bv_split_goal},
        { suffices : Γ_4 ≤ - (w₁ =ᴮ v₁),
            by {exact bv_absurd (w₁ =ᴮ v₁) ‹_› ‹_›},
          suffices : Γ_4 ≤ w₁ =ᴮ (func x i₁) ∧ Γ_4 ≤ v₁ =ᴮ (func x i₂),
            by { clear_except H_inj this h,
                 apply bv_rw' this.left, by simp,
                 apply bv_rw' this.right, by simp,
                 suffices H_le_bot : (func x i₁ =ᴮ func x i₂) ≤ ⊥,
                   by {rw[<-imp_bot, <-deduction], from le_trans (by simp) H_le_bot},
                 suffices H_not_bot_lt : ¬ (⊥ < func x i₁ =ᴮ func x i₂),
                   by {clear_except H_not_bot_lt, finish[bot_lt_iff_not_le_bot]},
                 clear_except H_inj h, intro H, from absurd (H_inj _ _ H) ‹_›},
          bv_split,
          refine ⟨eq_of_eq_pair_left' H_mem_left_1_right,
                   bv_context_trans (bv_symm H_eq) (eq_of_eq_pair_left' this_1_right)⟩}}
end

end lemmas

namespace pfun

section pfun_lemmas

/- Two partial functions are equal if their graphs are equal -/
lemma ext_graph {α β : Type*} (f g : α →. β) (h_graph : f.graph = g.graph) : f = g :=
  pfun.ext $ λ _ _, iff_of_eq (congr_fun h_graph (_,_))

lemma graph_empty_iff_dom_empty {α β : Type*} (f : α →. β) : f.graph = ∅ ↔ f.dom = ∅ :=
begin
  have := dom_iff_graph f,
  split; intro; ext; safe, from this _ _ ‹_›
end

/- A functional graph is a univalent graph -/
def functional {α β : Type*} (Γ : set (α × β)) : Prop :=
  ∀ a b₁ b₂, (a, b₁) ∈ Γ → (a, b₂) ∈ Γ → b₁ = b₂

lemma congr_arg {α β : Type*} (f : α →. β) : ∀ {x} {y} (h₁ : x ∈ f.dom) (h₂ : y ∈ f.dom)
  (h_eq : x = y), fn f x h₁ = fn f y h₂ :=
by intros; congr; assumption

lemma functional_subset {α β : Type*} (Γ Γ': set (α × β)) (h_Γ' : Γ' ⊆ Γ) (h_Γ : functional Γ) : functional Γ' :=
  λ _ _ _ _ _, by apply h_Γ; tidy

/-- The graph of a pfun is always functional -/
lemma graph_functional {α β : Type*} (f : α →. β) : functional f.graph := by tidy

/-- Given a partial functional relation, turn it into a pfun -/
noncomputable def of_graph {α β : Type*} (Γ : set (α × β)) (h_Γ : functional Γ) : α →. β :=
  λ a, ⟨∃ c ∈ Γ, (prod.fst c) = a, λ h, @prod.snd α β $ (classical.indefinite_description _ h).val⟩

lemma of_graph_property {α β : Type*} (Γ : set $ α × β) (h_Γ : functional Γ) (a : α) (h : ∃ c ∈ Γ, (prod.fst c) = a) : ∃ (H : Γ (classical.indefinite_description _ h)), (classical.indefinite_description _ h).val.fst = a :=
  by apply (classical.indefinite_description _ h).property

lemma of_graph_get {α β : Type*} (Γ : set $ α × β) (h_Γ : functional Γ) (a : α) : ∀ h,
(of_graph Γ h_Γ a).get h = (classical.indefinite_description _ h).val.snd :=
  by intro; refl

lemma of_graph_val {α β : Type*} (Γ : set $ α × β) (h_Γ : functional Γ) (a : α) (h : ∃ c ∈ Γ, (prod.fst c) = a) (c' ∈ Γ) (h' : c'.1 = a) :
  @prod.snd α β (classical.indefinite_description _ h).val = c'.snd :=
begin
  let c'', swap, change (prod.snd c'' = c'.snd),
  apply h_Γ a, swap, convert H, ext, rwa[h'], refl,
  have := (classical.indefinite_description _ h).property,
  cases this with this1 this2, rw[<-this2], convert this1, ext; refl
end

@[simp]lemma graph_of_graph {α β : Type*} (Γ : set $ α × β) (h_Γ : functional Γ) : (of_graph Γ h_Γ).graph = Γ :=
begin
  ext, rcases x with ⟨a,b⟩, dsimp[graph],
  split; intro H, {cases H, induction H_h, cases H_w, cases H_w_h, induction H_w_h_h,
  convert H_w_h_w, ext, refl, rw[of_graph_get], apply of_graph_val; try{assumption}; refl},
  fsplit, {tidy}, rw[of_graph_get], apply @of_graph_val _ _ Γ _ a _ (a,b) _;
  try{assumption}; refl
end

@[simp]lemma of_graph_graph {α β : Type*} {f : α →. β} : of_graph (f.graph) (graph_functional f) = f :=
  by apply ext_graph; rw[graph_of_graph]

@[simp]lemma dom_of_graph {α β : Type*} (Γ : set $ α × β) (h_Γ : functional Γ) : (of_graph Γ h_Γ).dom = (prod.fst '' Γ) :=
begin
 ext, split; intros, {tidy},
 {cases a, cases a_h, cases a_w, induction a_h_right, dsimp at *, fsplit,
 work_on_goal 0 { fsplit }, work_on_goal 2 {fsplit,
 work_on_goal 0 { assumption }, refl }}
end

@[simp]lemma dom_of_graph_union {α β : Type*} (Γ : set $ α × β) (p : α × β) (h_Γ : functional Γ) (h_Γ' : functional $ Γ ∪ {p}) : (of_graph (Γ ∪ {p}) h_Γ').dom = (of_graph Γ h_Γ).dom ∪ {p.fst} :=
  by simp[dom_of_graph, set.image_insert_eq]

lemma in_dom_of_in_graph {α β : Type*} {f : α →. β} : ∀ {a} {b}, (a,b) ∈ f.graph → a ∈ f.dom :=
  by {intros a b H, apply (pfun.dom_iff_graph _ a).mpr, exact ⟨b,H⟩}

lemma lift_graph' {α β : Type*} {f : α →. β} {a : α} {b : β} (h_a : a ∈ f.dom) : (a,b) ∈ f.graph ↔ pfun.fn f a h_a = b := by tidy

variables {α β : Type u}

def is_extension_of (f₁ f₂ : α →. β) : Prop := ∃ (H : f₁.dom ⊆ f₂.dom), restrict f₂ H = f₁

/-
TODO(jesse) avoid tactic mode and use classical.indefinite_description explicitly
-/
noncomputable def union_of_omega_chain (f : ℕ → α →. β) : α →. β :=
λ x, { dom := x ∈ (set.Union (λ k, (f k).dom) : set α),
  get := λ H,
  begin
    choose some_dom H_mem₁ H_mem₂ using H,
    choose k Hk₁ using H_mem₁, subst Hk₁,
    from fn (f k) x ‹_›
  end}
/-
TODO(jesse) rework this in terms of graphs of pfuns instead
-/
lemma union_of_omega_chain_spec (f : ℕ → α →. β) (H_chain : ∀ (k₁ k₂) (H_le : k₁ ≤ k₂), is_extension_of (f k₁) (f k₂)) :
∀ k, is_extension_of (f k) (union_of_omega_chain f):=
begin
  intro k, fsplit, change _ ⊆ set.Union _,
    {/- `tidy` says -/ intros a a_1, simp at *, fsplit, work_on_goal 1 { assumption }},
  ext1, sorry
end

end pfun_lemmas

end pfun

local prefix `#`:50 := cardinal.mk

section collapse_poset
variables X Y : Type u

structure collapse_poset : Type u :=
(f        : pfun X Y)
(Hc       : #f.dom ≤ (aleph 0))

open pfun

variables {X Y}
def collapse_poset.extends (p : collapse_poset X Y) (f : X → Y) : Prop :=
∀ (x : X) (H_x : x ∈ p.f.dom), f x = (fn p.f x H_x)

def collapse_poset.principal_open (p : collapse_poset X Y) : set (X → Y) :=
{f | collapse_poset.extends p f}

def collapse_space : topological_space (X → Y) :=
generate_from $ collapse_poset.principal_open '' set.univ

local attribute [instance, priority 9001] collapse_space

def collapse_space_basis : set $ set (X → Y) := collapse_poset.principal_open '' set.univ

def collapse_space_basis_spec : @is_topological_basis (X → Y) collapse_space collapse_space_basis := sorry

open collapse_poset

def one_point_pfun (x : X) (y : Y) : X →. Y :=
λ a, { dom := a = x,
       get := λ _, y }

@[simp]lemma one_point_pfun.eval {x a : X} {y : Y} (H_a : a = x) : fn (one_point_pfun x y) a H_a = y := by refl

def one_point_collapse_poset (x : X) (y : Y) : collapse_poset X Y :=
{ f := one_point_pfun x y,
  Hc := by {unfold one_point_pfun, tidy, from 0} }

lemma one_point_collapse_poset_principal_open {x : X} {y : Y} :
  (principal_open $ one_point_collapse_poset x y) = {g | g x = y} :=
begin
  ext, dsimp at *, fsplit, work_on_goal 0 { intros a }, work_on_goal 1 { intros a x_2 H_x, induction H_x, assumption }, sorry
end

lemma is_regular_one_point_regular_open {x : X} {y : Y} :
  is_regular (principal_open (one_point_collapse_poset x y)) :=
begin
  sorry
end

/--
Given a partial function f : X →. Y and a point y : Y, define an extension g of f to X such that g(x) = y whenever x ∉ f.dom
-/
noncomputable def trivial_extension (f : X →. Y) (y : Y) : X → Y :=
λ x,
  begin
    haveI : decidable (x ∈ f.dom) := classical.prop_decidable _,
    by_cases x ∈ f.dom,
      { exact fn f x ‹_› },
      { exact y }
  end

lemma trivial_extension_mem_principal_open {p : collapse_poset X Y} {y : Y}
  : (trivial_extension p.f y) ∈ collapse_poset.principal_open p :=
by unfold trivial_extension; tidy; simp*

lemma exists_mem_compl_dom_of_unctbl (p : collapse_poset X Y) (H_card : (aleph 0) < #X) :
  ∃ x : X, x ∉ p.f.dom :=
exists_mem_compl_of_mk_lt_mk _ $ lt_of_le_of_lt p.Hc ‹_›

end collapse_poset

local attribute [instance, priority 9000] collapse_space

section collapse_algebra
variables X Y : Type u

def collapse_algebra := @regular_opens (X → Y) collapse_space

variables {X Y}

@[instance, priority 9000] def collapse_algebra_boolean_algebra [H_nonempty : nonempty (X → Y)] : nontrivial_complete_boolean_algebra (collapse_algebra X Y) :=
regular_open_algebra H_nonempty

end collapse_algebra

private def 𝔹 : Type u := collapse_algebra ((ℵ₁ : pSet.{u}).type) (powerset omega : pSet.{u}).type

instance nonempty_aleph_one_powerset_omega : nonempty $ ((ℵ₁).type) → (powerset omega).type :=
⟨λ _, by {unfold pSet.omega, from λ _, false}⟩ 

instance 𝔹_boolean_algebra : nontrivial_complete_boolean_algebra 𝔹 :=
by unfold 𝔹; apply_instance

namespace collapse_algebra

lemma π_χ_regular (p : type (card_ex (aleph 1)) × (powerset omega).type) : @_root_.is_regular _ collapse_space {g : type (card_ex (aleph 1)) → type (powerset omega) | g (p.fst) = p.snd} :=
begin
  let A := (collapse_poset.principal_open (one_point_collapse_poset (p.fst) (p.snd))),
  sorry
end

def π_χ : ((ℵ₁ : pSet.{u}).type × (pSet.powerset omega : pSet.{u}).type) → 𝔹 :=
λ p, ⟨{g | g p.1 = p.2}, π_χ_regular _⟩

private lemma eq₀ : ((ℵ₁)̌  : bSet 𝔹).type = (ℵ₁).type := by simp

private lemma eq₀' : ((powerset omega)̌  : bSet.{u} 𝔹).type = (powerset omega).type := by simp

private lemma eq₁ : (((ℵ₁)̌  : bSet 𝔹).type × ((powerset omega)̌  : bSet 𝔹).type) = ((ℵ₁ .type) × (powerset omega).type) := by simp

lemma aleph_one_type_uncountable : (aleph 0) < # ℵ₁.type :=
by simp only [cardinal.aleph_zero, pSet.omega_lt_aleph_one, pSet.mk_type_mk_eq''']

@[reducible]def π_af : ((ℵ₁̌  : bSet 𝔹) .type) → ((powerset omega)̌  : bSet 𝔹) .type → 𝔹 :=
λ η S, (⟨{g | g (cast eq₀ η) = (cast eq₀' S)}, sorry⟩ : 𝔹)

lemma π_af_wide :  ∀ (j : ((powerset omega)̌ ).type), (⨆ (i : type (ℵ₁̌ )), π_af i j) = (⊤ : 𝔹) :=
begin
 intro S,
   refine Sup_eq_top_of_dense_Union _,
   apply dense_of_dense_in_basis _ collapse_space_basis_spec _,
   intros B HB HB_ne,
   unfold collapse_space_basis at HB, cases HB with p Hp, simp at Hp, subst Hp,
   refine set.ne_empty_of_exists_mem _,
   { cases exists_mem_compl_dom_of_unctbl p aleph_one_type_uncountable with η Hη,
     use trivial_extension p.f S, use trivial_extension_mem_principal_open,
     change ∃ x, _, use (π_af (cast eq₀.symm η) S).val,
     refine ⟨_, _⟩, change ∃ x, _, refine ⟨_,_⟩,
     apply π_af (cast eq₀.symm η) S, refine ⟨_,_⟩,
       { exact set.mem_range_self _ },
       { refl },
     { unfold trivial_extension, dsimp,
       suffices this : (cast eq₀ (cast eq₀.symm η) ∉ pfun.dom (p.f)),
         by {simp*, refl},
       intro, apply Hη, cc} }
end

lemma π_af_anti : ∀ (i : type (ℵ₁̌  : bSet 𝔹)) (j₁ j₂ : type ((powerset omega)̌ )),
    j₁ ≠ j₂ → π_af i j₁ ⊓ π_af i j₂ ≤ ⊥ :=
λ _ _ _ _ _ h, by cases h; finish

lemma aleph_one_inj : (∀ i₁ i₂, ⊥ < (func (ℵ₁̌  : bSet 𝔹) i₁) =ᴮ (func (ℵ₁̌  : bSet 𝔹) i₂) → i₁ = i₂) :=
begin
  suffices this : ∀ (x y : type (ℵ₁)),
    x ≠ y → ¬equiv (func (ℵ₁) x) (func (ℵ₁) y),
    by {intros i₁ i₂ H, haveI : decidable (i₁ = i₂) := classical.prop_decidable _,
        by_contra, 
        have H_cast_eq : (cast eq₀ i₁) ≠ (cast eq₀ i₂),
          by {intro, apply a, cc},
        specialize this (cast eq₀ i₁) (cast eq₀ i₂) ‹_›,
        have this₀ := check_bv_eq_bot_of_not_equiv this,
        suffices this₁ : func (ℵ₁̌ ) i₁ =ᴮ func (ℵ₁̌ ) i₂ = ⊥,
          by {exfalso, rw[eq_bot_iff] at this₀, rw[bot_lt_iff_not_le_bot] at H,
              suffices : func (ℵ₁̌  : bSet 𝔹) i₁ =ᴮ func (ℵ₁ ̌) i₂ ≤ ⊥, by contradiction,
              change_congr (func ℵ₁ (cast eq₀ i₁))̌   =ᴮ (func ℵ₁ (cast eq₀ i₂)) ̌ ≤ ⊥,
              apply check_func, apply check_func, from ‹_›},
        convert this₀; apply check_func},
  exact λ _ _ _, ordinal.mk_inj _ _ _ ‹_›
end

noncomputable def π : bSet 𝔹 :=
rel_of_array (ℵ₁̌  : bSet 𝔹) ((powerset omega)̌ ) π_af

-- noncomputable def π : bSet 𝔹 := @set_of_indicator (𝔹 : Type u) _ (prod (ℵ₁̌ ) ((powerset omega)̌ )) (λ z, π_χ (cast eq₁ z))

lemma π_is_func {Γ} : Γ ≤ is_func π :=
begin
  unfold π, refine rel_of_array_extensional _ _ _ (by simp) (by simp) _ _ _,
  { from π_af_wide },
  { from π_af_anti },
  { from aleph_one_inj },
end

lemma π_is_functional {Γ} : Γ ≤ is_functional π := is_functional_of_is_func _ π_is_func

lemma π_is_surj {Γ} : Γ ≤ is_surj (ℵ₁̌ ) ((powerset omega)̌ ) π :=
rel_of_array_surj _ _ _ (by simp) (by simp) (π_af_wide)

lemma π_spec {Γ : 𝔹} : Γ ≤ (is_func π) ⊓ ⨅v, v ∈ᴮ (powerset omega)̌  ⟹ (⨆w, w ∈ᴮ (ℵ₁̌ ) ⊓ pair w v ∈ᴮ π) := le_inf π_is_func π_is_surj

lemma ℵ₁_larger_than_continuum {Γ : 𝔹} : Γ ≤ larger_than (ℵ₁ ̌) ((powerset omega)̌ ) :=
by apply bv_use π; from π_spec

-- for these two lemmas, need 2.17 (iv) in Bell, which follows from (i) ⟹ (ii)
-- i.e. If 𝔹 has a dense subset P which is ω-closed, then for any η < ℵ₁, and any x,
-- bSet 𝔹 ⊩ Func(η̌, x̌) = Func(η, x)̌ .

/-
Proof sketch:
Let p : P be such that p ⊩ f is a function from η̌ to x̌. Using the ω-closed assumption, find a descending sequence {p_i : P} and a set {y_i ∈ x} such that for each i, pᵢ ⊩ f(i) = y_i.

If q ∈ P satisfies q ≤ pᵢ for all i (i.e. is a witness to the ω-closed assumption),
and g is the function attached to the collection of pairs (i, y_i), show that q ⊩ f = ǧ.
-/

def function_reflect (g : bSet 𝔹) (x y : pSet) {Γ} (H : Γ ≤  is_func' (x̌) (y̌) g) : pSet := sorry

lemma function_reflect_spec {g} {x y} {Γ : 𝔹} (H : Γ ≤ _) : Γ ≤ (function_reflect g x y H)̌  =ᴮ g :=
sorry

lemma function_reflect_surj_of_surj {g} {x y} {Γ : 𝔹} (H : Γ ≤ _) (H_not_zero : ⊥ < Γ) (H_surj : Γ ≤ is_surj (x̌) (y̌) (g : bSet 𝔹)) :
  pSet.is_surj x y (function_reflect g x y H) :=
sorry

lemma ex_no_surj_omega_aleph_one : ¬ ∃ f : pSet, pSet.is_surj (pSet.omega) (ordinal.mk (aleph 1).ord) f :=
begin
  intro H, cases H with f Hf, dsimp[pSet.is_surj] at Hf, sorry
end


--TODO(jesse) check that this proof actually works
lemma omega_lt_aleph_one {Γ : 𝔹} : Γ ≤ bSet.omega ≺ (ℵ₁̌ ) :=
begin
  unfold larger_than, rw[<-imp_bot], rw[<-deduction], /- `tidy_context` says -/ refine poset_yoneda _, intros Γ_1 a, simp only [le_inf_iff] at *, cases a,
  bv_cases_at a_right f, rw[le_inf_iff] at a_right_1, cases a_right_1,
  by_contra, replace a := (bot_lt_iff_not_le_bot.mpr a),
  suffices this : ∃ f : pSet, pSet.is_surj (pSet.omega) (ordinal.mk (aleph 1).ord) f,
    by {exfalso, from ex_no_surj_omega_aleph_one ‹_›},
  let g := (function_reflect f (pSet.omega) (ordinal.mk (aleph 1).ord) sorry),
  use g,
  apply function_reflect_surj_of_surj, from ‹_›, from a_right_1_right
end


lemma aleph_one_check_universal_property (Γ : 𝔹) : Γ ≤ aleph_one_universal_property (ℵ₁̌  : bSet 𝔹) :=
begin
  apply bv_rw' (aleph_one_check_is_aleph_one_of_omega_lt (omega_lt_aleph_one)),
  { simp },
  { from aleph_one_satisfies_universal_property }
end

lemma continuum_is_continuum {Γ : 𝔹} : Γ ≤ (pSet.powerset omega)̌  =ᴮ (bv_powerset bSet.omega) :=
begin
  refine subset_ext (check_powerset_subset_powerset _) _,
  bv_intro χ, bv_imp_intro H_χ,
  suffices this : ∃ S : (powerset omega).type, Γ_1 ≤  (set_of_indicator χ) =ᴮ ((powerset omega).func S)̌ ,
    by { cases this with S HS, apply bv_use S, rwa[top_inf_eq] },
  sorry -- TODO(jesse): come up with a specialized argument for this
end

theorem CH_true : (⊤ : 𝔹) ≤ CH :=
begin
  refine CH_true_aux _ _,
    { from aleph_one_check_universal_property },
    { intro Γ, rw[<-imp_bot],
      bv_imp_intro,
      suffices ex_surj : Γ_1 ≤ larger_than (ℵ₁̌ ) (𝒫 ω),
        by {dsimp [Γ_1] at H ex_surj ⊢, bv_contradiction},
      apply bv_rw' (bv_symm continuum_is_continuum),
        { from B_ext_larger_than_right },
        { from ℵ₁_larger_than_continuum }}
end

end collapse_algebra
