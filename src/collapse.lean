import .regular_open_algebra .pSet_ordinal

/-
  Defining the collapsing poset/topology/boolean algebra and proving properties about them
-/

universe u

open lattice topological_space cardinal pSet

@[reducible]private noncomputable definition ℵ₁ : pSet := (card_ex $ aleph 1)

local infix ` ⟹ `:65 := lattice.imp

local infix ` ⇔ `:50 := lattice.biimp

local attribute [instance, priority 0] classical.prop_decidable

namespace pfun

section pfun_lemmas

/- Two partial functions are equal if their graphs are equal -/
lemma ext_graph {α β : Type*} (f g : α →. β) (h_graph : f.graph = g.graph) : f = g :=
  pfun.ext $ λ _ _, iff_of_eq $ congr_fun h_graph (_,_)

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
(take a union of the graphs, extract a pfun)
-/
lemma union_of_omega_chain_spec (f : ℕ → α →. β) (H_chain : ∀ (k₁ k₂) (H_le : k₁ ≤ k₂), is_extension_of (f k₁) (f k₂)) :
∀ k, is_extension_of (f k) (union_of_omega_chain f):=
begin
  intro k, fsplit, change _ ⊆ set.Union _,
    {/- `tidy` says -/ intros a a_1, simp at *, fsplit, work_on_goal 1 { assumption }},
  ext1, sorry
end

lemma fn_mem_ran {X Y} {f : X →. Y} {x : X} {Hx : x ∈ f.dom} :
  (fn f x Hx) ∈ f.ran :=
by use x; tidy

end pfun_lemmas

end pfun

local prefix `#`:50 := cardinal.mk

section collapse_poset
variables X Y : Type u

structure collapse_poset : Type u :=
(f        : X →. Y)
(Hc       : #f.dom ≤ (aleph 0))

def collapse_poset.empty {α β : Type u} : collapse_poset α β :=
{ f := λ x, roption.none,
  Hc := by { change # (∅ : set α) ≤ _, simp } }

open pfun

variables {X Y}

/- TODO: separate out the lemma `#f.ran ≤ #f.dom` -/
lemma collapse_poset.ran_ctbl (p : collapse_poset X Y) : # p.f.ran ≤ aleph 0 :=
begin
  suffices : #p.f.ran ≤ #p.f.dom,
    by {exact le_trans this p.Hc},
  refine mk_le_of_surjective _,
    { exact λ ⟨x,H⟩, ⟨fn p.f x H, by apply fn_mem_ran⟩},
    { intros y, by_contra, push_neg at a,
    /- `tidy` says -/ cases y, cases y_property, cases y_property_h,
      induction y_property_h_h, simp at *, dsimp at *,
      specialize a ‹_› ‹_›, finish }
end

def collapse_poset.inter (p₁ p₂ : collapse_poset X Y) : collapse_poset X Y :=
{ f := λ x, { dom := ∃ (H₁ : p₁.f.dom x) (H₂ : p₂.f.dom x), (fn p₁.f x H₁ = fn p₂.f x H₂), get := λ H, by {refine fn p₁.f x (by tidy)}},
  Hc := by {refine le_trans _ p₁.Hc, exact mk_le_mk_of_subset (by tidy)}}

@[reducible]def collapse_poset.compatible (p₁ p₂ : collapse_poset X Y) : Prop :=
∀ x (H₁ : p₁.f.dom x) (H₂ : p₂.f.dom x), p₁.f.fn x H₁ = p₂.f.fn x H₂

@[simp]lemma dom_reduce {D : X → Prop} {D_get : Π x (H : D x), Y} : pfun.dom (λ x, roption.mk (D x) (D_get x) : X →. Y) = D := rfl

@[simp]lemma fn_reduce {D : X → Prop} {D_get : Πx (H : D x), Y} {x} {H} : pfun.fn (λ x, roption.mk (D x) (D_get x) : X →. Y) x H = D_get x H := rfl

noncomputable def collapse_poset.join (p₁ p₂ : collapse_poset X Y)
  (H_compat : collapse_poset.compatible p₁ p₂) : collapse_poset X Y :=
{ f := λ x, { dom := (p₁.f.dom x ∨ p₂.f.dom x),
              get := λ H, dite (p₁.f.dom x) (λ H, p₁.f.fn x H)
                               (λ H', p₂.f.fn x (or.resolve_left H ‹_›))},
  Hc := by rw[aleph_zero]; apply mk_union_countable_of_countable;
             [convert p₁.Hc, convert p₂.Hc]; rw[aleph_zero] }

@[simp]lemma mem_dom_join_of_mem_left {p₁ p₂ : collapse_poset X Y} {x} (Hx : p₁.f.dom x)
  (H_compat : collapse_poset.compatible p₁ p₂) : (collapse_poset.join p₁ p₂ H_compat).f.dom x :=
by finish[collapse_poset.join]

@[simp]lemma mem_dom_join_of_mem_right {p₁ p₂ : collapse_poset X Y} {x} (Hx : p₂.f.dom x)
  (H_compat : collapse_poset.compatible p₁ p₂) : (collapse_poset.join p₁ p₂ H_compat).f.dom x :=
by finish[collapse_poset.join]

lemma exists_mem_compl_dom_of_unctbl (p : collapse_poset X Y) (H_card : (aleph 0) < #X) :
  ∃ x : X, x ∉ p.f.dom :=
exists_mem_compl_of_mk_lt_mk _ $ lt_of_le_of_lt p.Hc ‹_›

lemma exists_mem_compl_ran_of_unctbl (p : collapse_poset X Y) (H_card : (aleph 0) < #Y) :
  ∃ y : Y, y ∉ p.f.ran :=
exists_mem_compl_of_mk_lt_mk _ $ lt_of_le_of_lt (collapse_poset.ran_ctbl _)  ‹_›

def collapse_poset.extends (p : collapse_poset X Y) (f : X → Y) : Prop :=
∀ (x : X) (H_x : x ∈ p.f.dom), f x = (fn p.f x H_x)

def collapse_poset.principal_open (p : collapse_poset X Y) : set (X → Y) :=
{f | collapse_poset.extends p f}

@[simp]lemma collapse_poset.principal_open_empty : collapse_poset.principal_open (collapse_poset.empty : collapse_poset X Y) = set.univ :=
begin
  ext f, split; intro H,
    { trivial },
    { tidy }
end

@[simp]lemma mem_principal_open_iff {p : collapse_poset X Y} {f : X → Y} : f ∈ (collapse_poset.principal_open p) ↔ ∀ (x : X) (H_x : x ∈ p.f.dom), f x = (fn p.f x H_x) := by refl

@[simp]lemma mem_ran_of_mem_dom {p : collapse_poset X Y} {f : X → Y} {x : X} (H : f ∈ collapse_poset.principal_open p) : x ∈ p.f.dom → f x ∈ p.f.ran :=
by { intro H_mem, rw[mem_principal_open_iff] at H,
     use x, rw[H _ ‹_›], from roption.get_mem H_mem }

def collapse_space : topological_space (X → Y) :=
generate_from $ collapse_poset.principal_open '' set.univ

local attribute [instance, priority 9001] collapse_space

@[simp]lemma collapse_poset.principal_open_is_open {p : collapse_poset X Y} : is_open (collapse_poset.principal_open p) :=
generate_open.basic _ ⟨p, trivial, rfl⟩

open collapse_poset

def one_point_pfun (x : X) (y : Y) : X →. Y :=
λ a, { dom := a = x,
       get := λ _, y }

@[simp]lemma one_point_pfun.eval {x a : X} {y : Y} (H_a : a = x) : fn (one_point_pfun x y) a H_a = y := by refl

def one_point_collapse_poset (x : X) (y : Y) : collapse_poset X Y :=
{ f := one_point_pfun x y,
  Hc := by {unfold one_point_pfun, tidy, from 0} }

@[simp]lemma one_point_collapse_poset_principal_open {x : X} {y : Y} :
  (principal_open $ one_point_collapse_poset x y) = {g | g x = y} :=
begin
  ext, dsimp at *, fsplit, work_on_goal 0 { intros a }, work_on_goal 1 { intros a x_2 H_x, induction H_x, assumption }, exact a x rfl
end

lemma collapse_poset.compl_principal_open_is_Union (p : collapse_poset X Y) : ∃ {ι : Type u} (s : ι → (collapse_poset X Y)), set.Union (λ i : ι, (principal_open $ s i)) = - (principal_open p) :=
begin
  use ({pr : X × Y // ∃ (H_mem : pr.1 ∈ p.f.dom), pr.2 ≠ (fn p.f pr.1 H_mem)}),
  use (λ s, one_point_collapse_poset s.1.1 s.1.2),
  ext f, split; intro H,
    { change _ ∉ _, intro H_mem,
      rcases H with ⟨P, ⟨⟨⟨x',y'⟩, ⟨H_mem₁, H_neq⟩⟩, Hpr⟩, H_mem₂⟩, subst Hpr,
      suffices this : y' = (fn p.f x' ‹_›),
        by { exact H_neq ‹_› },
      rw[<-show f x' = y', by simpa using H_mem₂],
      from mem_principal_open_iff.mpr H_mem _ _ },
    { change _ → false at H, rw[mem_principal_open_iff] at H,
      change ¬ _ at H, push_neg at H, rcases H with ⟨x, Hx, H_neq⟩,
      suffices this : ∃ (a : X) (H_mem : (a, f a).fst ∈ dom (p.f)), ¬f a = fn (p.f) a H_mem,
        by simpa,
      from ⟨_, by use ‹_›⟩ }
end

@[simp]lemma collapse_poset.principal_open_is_closed {p : collapse_poset X Y} : is_closed (collapse_poset.principal_open p) :=
by  {rcases collapse_poset.compl_principal_open_is_Union p with ⟨ι, ⟨s, Hu⟩⟩,
     rw[is_closed, <-Hu], simp[is_open_Union]}

@[simp] lemma collapse_poset.is_regular_principal_open (p : collapse_poset X Y) : is_regular (collapse_poset.principal_open p) :=
by simp[is_clopen]

--   simp[join], refine ⟨_,_⟩,
--     { from or.inl ‹_› },
--     { intro H, solve_by_elim }
-- end

lemma inter_principal_open {p₁ p₂ : collapse_poset X Y} (H : compatible p₁ p₂) : principal_open p₁ ∩ principal_open p₂ = principal_open (join p₁ p₂ H) :=
begin
  ext f; split; intro H_mem,
    { rw mem_principal_open_iff, intros x H_x, simp[join] at H_x ⊢,
      cases H_x, cases H_mem,
        { simp*, solve_by_elim },
        { by_cases p₁.f.dom x; cases H_mem; simp*; solve_by_elim }},
    { refine ⟨_,_⟩,
        all_goals{rw[mem_principal_open_iff] at ⊢ H_mem, intros x Hx, specialize H_mem x},
          { specialize H_mem (mem_dom_join_of_mem_left ‹_› ‹_›),
            change p₁.f.dom x at Hx, refine eq.trans H_mem _,
            simp[*, join] },
          { specialize H_mem (mem_dom_join_of_mem_right ‹_› ‹_›),
            change p₂.f.dom x at Hx, by_cases p₁.f.dom x,
            { rw[<-H], rw[H_mem], simp[join, h], from ‹_› },
            { rw[H_mem], simp[join, h] }}}
end

def collapse_space_basis : set $ set (X → Y) := insert (∅ : set (X → Y)) (collapse_poset.principal_open '' set.univ)

def collapse_space_basis_spec : @is_topological_basis (X → Y) collapse_space collapse_space_basis :=
begin
  refine ⟨λ P HP P' HP' f H_mem_inter, _,_,_⟩,
    { rw[collapse_space_basis] at HP HP',
      cases HP; cases HP',

        { suffices this : f ∈ (∅ : set $ X → Y),
            by {cases this}, substs HP, cases H_mem_inter, from ‹_› },
        { suffices this : f ∈ (∅ : set $ X → Y),
            by {cases this}, substs HP, cases H_mem_inter, from ‹_› },
        { suffices this : f ∈ (∅ : set $ X → Y),
            by {cases this}, substs HP', cases H_mem_inter, from ‹_› },

      simp only [set.image_univ, set.mem_range] at HP HP',
      cases HP with y Hy; cases HP' with y' Hy',

      substs Hy Hy', use (principal_open y ∩ principal_open y'),
      refine ⟨_,⟨‹_›,(by refl)⟩⟩,
       { by_cases H_compat : (compatible y y'),
           { right, refine ⟨_,⟨trivial, _⟩⟩, from join y y' ‹_›, rw[inter_principal_open] },
           { suffices this : principal_open y ∩ principal_open y' = ∅,
               by {rw[this], from or.inl rfl },
             ext g; split; intro H,
               { exfalso, cases H with H₁ H₂, simp at H₁ H₂,
                 push_neg at H_compat, rcases H_compat with ⟨x, Hx₁, Hx₂, Hx₃⟩,
                 apply Hx₃, transitivity g x; solve_by_elim },
               { cases H }}}},

    { refine le_antisymm (λ _ _, trivial) _,
      intros f _a, refine ⟨_,_⟩,
      { exact (principal_open collapse_poset.empty) },
      { refine ⟨by {rw[collapse_space_basis], right, exact set.mem_image_univ},_⟩, simp }},
    { unfold collapse_space_basis collapse_space, refine le_antisymm _ _,
      { refine generate_from_mono _, from λ _ _, or.inr ‹_›},
      { intros T HT, induction HT,
        { cases HT_H, subst HT_H, exact is_open_empty, constructor, from ‹_› },
        { exact is_open_univ },
        { apply generate_open.inter, from ‹_›, from ‹_› },
        { apply generate_open.sUnion, intros S HS, solve_by_elim }}}
end

@[simp]lemma is_regular_one_point_regular_open {x : X} {y : Y} :
  is_regular (principal_open (one_point_collapse_poset x y)) :=
collapse_poset.is_regular_principal_open _

@[simp]lemma is_regular_one_point_regular_open' {x : X} {y : Y} :
  is_regular {g : X → Y | g x = y} :=
by {rw[<-one_point_collapse_poset_principal_open], from is_regular_one_point_regular_open}

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

end collapse_poset

local attribute [instance, priority 9000] collapse_space

section collapse_algebra
variables X Y : Type u

def collapse_algebra := @regular_opens (X → Y) collapse_space

variables {X Y}

@[instance, priority 9001] def collapse_algebra_boolean_algebra [nonempty (X → Y)] : nontrivial_complete_boolean_algebra (collapse_algebra X Y) :=
regular_open_algebra ‹_›

end collapse_algebra

def collapse_poset.inclusion {X Y : Type u} : collapse_poset X Y → collapse_algebra X Y :=
λ p, ⟨collapse_poset.principal_open p, collapse_poset.is_regular_principal_open p⟩

local notation `ι`:65 := collapse_poset.inclusion

lemma collapse_poset_dense_basis {X Y : Type u} : ∀ T ∈ @collapse_space_basis X Y,
  ∀ h_nonempty : T ≠ ∅, ∃ p : collapse_poset X Y, (ι p).val ⊆ T :=
begin
  intros T H_mem_basis _,
  refine or.elim H_mem_basis (λ _, (false.elim (absurd ‹T = ∅› ‹_›))) (λ H, _),
  rcases H with ⟨_,⟨_,H₂⟩⟩, from ⟨‹_›, by simp[H₂, collapse_poset.inclusion]⟩
end

lemma collapse_poset_dense {X Y : Type u} [nonempty (X → Y)] {b : collapse_algebra X Y}
  (H : ⊥ < b) : ∃ p : (collapse_poset X Y), ι p ≤ b :=
begin
  cases (classical.choice (classical.nonempty_of_not_empty _ H.right.symm)) with S_wit H_wit,
  change ∃ p, (ι p).val ⊆ b.val,
  have := mem_basis_subset_of_mem_open (collapse_space_basis_spec) H_wit (is_open_of_is_regular b.property),
  rcases (mem_basis_subset_of_mem_open
           (collapse_space_basis_spec) H_wit (is_open_of_is_regular b.property))
         with ⟨v, Hv₁, Hv₂, Hv₃⟩,
  have : v ≠ ∅, by {intro H, rw[H] at Hv₂, cases Hv₂},
  cases (collapse_poset_dense_basis ‹_› ‹_› ‹_›) with p H_p, from ⟨p, set.subset.trans H_p ‹_›⟩
end

local notation `𝔹` := collapse_algebra ((ℵ₁ : pSet).type) (powerset omega : pSet).type

instance nonempty_aleph_one_powerset_omega : nonempty $ ((ℵ₁).type) → (powerset omega).type :=
⟨λ _, by {unfold pSet.omega, from λ _, false}⟩

def 𝔹_boolean_algebra : nontrivial_complete_boolean_algebra 𝔹 :=
by apply_instance

