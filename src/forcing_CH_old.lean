import .bvm .bvm_extras .regular_open_algebra .to_mathlib data.pfun tactic

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

theorem CH_true_aux {β} [nontrivial_complete_boolean_algebra β]
  (H_aleph_one : ∀{Γ : β}, Γ ≤ aleph_one_universal_property (ℵ₁̌ ))
  (H_not_lt    : ∀{Γ : β}, Γ ≤ - ((ℵ₁)̌  ≺ 𝒫(ω)))
  : ∀{Γ : β}, Γ ≤ CH :=
begin
  intro Γ, unfold CH, rw[<-imp_bot], bv_imp_intro,
  bv_cases_at H x, bv_cases_at H_1 y, clear H H_1, bv_split, bv_split,
  unfold aleph_one_universal_property at H_aleph_one,
  replace H_aleph_one := @H_aleph_one Γ_3 x ‹_›,
  suffices H_aleph_one_lt_continuum : Γ_3 ≤ (ℵ₁)̌  ≺ 𝒫(ω),
    from bv_absurd _ H_aleph_one_lt_continuum H_not_lt,
  from bSet_lt_of_lt_of_le _ y _ (bSet_lt_of_le_of_lt _ x _ ‹_› ‹_›) ‹_›
end

section lemmas

variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

/-- Corresponds to proposition 5.2 in Moore's 'the method of forcing':
Let x be a set and let ϕ(v) be a formula in the forcing language. If ∀ y ∈ x, p ⊩ ϕ(y̌), then p ⊩ ∀ y ∈ (x̌), ϕ(y)
-/
lemma check_forall (x : pSet) (ϕ : bSet 𝔹 → 𝔹) {h : B_ext ϕ} {b : 𝔹} :
  (∀ (y : x.type), b ≤ ϕ((x.func y)̌ )) → (b ≤ (⨅(y : x.type), ϕ((x.func y)̌ ))) := λ H, le_infi ‹_›

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

section collapse_poset
variables X Y : Type u

structure collapse_poset : Type u :=
(f        : pfun X Y)
(Hc       : set.countable f.dom)

open pfun

variables {X Y}
def collapse_poset.extends (p : collapse_poset X Y) (f : X → Y) : Prop :=
∀ (x : X) (H_x : x ∈ p.f.dom), f x = (fn p.f x H_x)

def collapse_poset.principal_open (p : collapse_poset X Y) : set (X → Y) :=
{f | collapse_poset.extends p f}

def collapse_space : topological_space (X → Y) :=
generate_from $ collapse_poset.principal_open '' set.univ

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
sorry

def π_χ : ((ℵ₁ : pSet.{u}).type × (pSet.powerset omega : pSet.{u}).type) → 𝔹 :=
λ p, ⟨{g | g p.1 = p.2}, π_χ_regular _⟩

private lemma eq₀ : ((ℵ₁)̌  : bSet 𝔹).type = (ℵ₁).type := by simp

private lemma eq₀' : ((powerset omega)̌  : bSet.{u} 𝔹).type = (powerset omega).type := by simp

private lemma eq₁ : (((ℵ₁)̌  : bSet 𝔹).type × ((powerset omega)̌  : bSet 𝔹).type) = ((ℵ₁ .type) × (powerset omega).type) := by simp

noncomputable def π : bSet 𝔹 := @set_of_indicator (𝔹 : Type u) _ (prod (ℵ₁̌ ) ((powerset omega)̌ )) (λ z, π_χ (cast eq₁ z))

lemma π_is_extensional {Γ} : Γ ≤ is_extensional π := sorry

lemma π_is_functional {Γ} : Γ ≤ is_functional π := sorry

lemma π_is_func {Γ} : Γ ≤ (is_func π) := le_inf π_is_extensional π_is_functional

lemma π_is_surj {Γ} : Γ ≤ ⨅v, v ∈ᴮ (powerset omega)̌  ⟹ ⨆ w, w ∈ᴮ (ℵ₁ ̌) ⊓ pair w v ∈ᴮ π :=
begin
  bv_intro v, bv_imp_intro, sorry
end

lemma π_spec {Γ : 𝔹} : Γ ≤ (is_func π) ⊓ ⨅v, v ∈ᴮ (powerset omega)̌  ⟹ (⨆w, w ∈ᴮ (ℵ₁̌ ) ⊓ pair w v ∈ᴮ π) := le_inf π_is_func π_is_surj

lemma ℵ₁_larger_than_continuum {Γ : 𝔹} : Γ ≤ larger_than (ℵ₁ ̌) ((powerset omega)̌ ) :=
by apply bv_use π; from π_spec

lemma aleph_one_is_aleph_one (Γ : 𝔹) : Γ ≤ aleph_one_universal_property (ℵ₁̌ ) := sorry

lemma continuum_is_continuum {Γ : 𝔹} : Γ ≤ (pSet.powerset omega)̌  =ᴮ (bv_powerset bSet.omega) := sorry

theorem CH_true : (⊤ : 𝔹) ≤ CH :=
begin
  refine CH_true_aux _ _,
    { from aleph_one_is_aleph_one },
    { intro Γ, rw[<-imp_bot],
      bv_imp_intro,
      suffices ex_surj : Γ_1 ≤ larger_than (ℵ₁̌ ) (𝒫 ω),
        by {dsimp [Γ_1] at H ex_surj ⊢, bv_contradiction},
      apply bv_rw' (bv_symm continuum_is_continuum),
        { from B_ext_larger_than_right },
        { from ℵ₁_larger_than_continuum }}
end

end collapse_algebra
