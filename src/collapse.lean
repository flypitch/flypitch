import .regular_open_algebra .pSet_ordinal

/-
  Defining the collapsing poset/topology/boolean algebra and proving properties about them
-/

universe variable u

open lattice topological_space cardinal pSet

noncomputable theory

local notation `ℵ₁` := (card_ex $ aleph 1 : pSet)

local infix ` ⟹ `:65 := lattice.imp

local infix ` ⇔ `:50 := lattice.biimp

local attribute [instance, priority 0] classical.prop_decidable

local prefix `#`:50 := cardinal.mk

/- to_mathlib -/
@[simp] lemma iff_or_self_left {p q : Prop} : (p ↔ p ∨ q) ↔ (q → p) :=
⟨ λ h hq, h.2 (or.inr hq), λ h, ⟨or.inl, λ h', h'.elim id h⟩⟩

@[simp] lemma iff_or_self_right {p q : Prop} : (p ↔ q ∨ p) ↔ (q → p) :=
by simp [or.comm]

@[simp] lemma and_iff_self_right {p q : Prop} : (p ∧ q ↔ p) ↔ (p → q) :=
⟨ λ h hp, (h.mpr hp).2, λ h, ⟨and.left, λ hp, ⟨hp, h hp⟩⟩⟩

@[simp] lemma and_iff_self_left {p q : Prop} : (p ∧ q ↔ q) ↔ (q → p) :=
by { rw [and.comm], exact and_iff_self_right }

lemma and_or_and_not {p q r : Prop} : p ∧ (q ∨ (r ∧ ¬ p)) ↔ p ∧ q :=
by simp [and_or_distrib_left, and.comm, and.assoc.symm]

lemma or_and_iff_or {p q r : Prop} : (p ∨ (q ∧ r) ↔ p ∨ q) ↔ (q → p ∨ r) :=
⟨ λ h hq, (h.2 (or.inr hq)).imp id and.right,
  λ h, ⟨λ h', h'.imp id and.left, λ h', h'.elim or.inl $ λ hq, (h hq).imp id $ λ hr, ⟨hq, hr⟩⟩⟩

lemma and_or_iff_and {p q r : Prop} : (p ∧ (q ∨ r) ↔ p ∧ r) ↔ (p → q → r) :=
⟨ λ h hp hq, (h.mp ⟨hp, or.inl hq⟩).2,
  λ h, ⟨λ h', ⟨h'.1, h'.2.elim (h h'.1) id⟩, and.imp id or.inr⟩⟩

lemma or_not_iff (p q : Prop) [decidable q] : (p ∨ ¬ q) ↔ (q → p) :=
by { rw [imp_iff_not_or, or_comm] }

lemma eq_iff_eq_of_eq_left {α} {x y z : α} (h : x = y) : x = z ↔ y = z :=
by rw [h]

lemma eq_iff_eq_of_eq_right {α} {x y z : α} (h : x = y) : z = x ↔ z = y :=
by rw [h]

namespace roption

variables {α : Type*} {o₁ o₂ : roption α} {x : α}
/-- The intersection of two partial functions -/
def inter (o₁ o₂ : roption α) : roption α :=
⟨ ∃(x : α), x ∈ o₁ ∧ x ∈ o₂,
  λ h, o₁.get $ dom_iff_mem.2 $ let ⟨x, h1x, h2x⟩ := h in ⟨x, h1x⟩⟩

instance : has_inter (roption α) := ⟨roption.inter⟩

lemma dom_inter : (o₁ ∩ o₂).dom ↔ ∃(x : α), x ∈ o₁ ∧ x ∈ o₂ := iff.refl _
lemma get_inter (h : ∃(x : α), x ∈ o₁ ∧ x ∈ o₂) :
  ∃(h' : o₁.dom), (o₁ ∩ o₂).get h = o₁.get h' := ⟨_, rfl⟩

@[simp] lemma mem_inter : x ∈ o₁ ∩ o₂ ↔ x ∈ o₁ ∧ x ∈ o₂ :=
begin
  split,
  { intro h, rw [mem_eq] at h, rcases h with ⟨⟨x, h1x, h2x⟩, rfl⟩,
    cases get_inter ⟨x, h1x, h2x⟩ with _h h2, rw [h2],
    split, { apply get_mem },
    rw [mem_eq] at h1x, rw [mem_eq] at h2x, cases h1x with _h2 h1x,
    cases h2x with _h3 h2x, rw [h1x, ← h2x], apply get_mem },
  { rintro ⟨h1, h2⟩, use ⟨x, h1, h2⟩,
    cases get_inter ⟨x, h1, h2⟩ with _h h3, rw [h3],
    rw [mem_eq] at h1, cases h1 with _h2 h1, exact h1 }
end

end roption

namespace pfun

section pfun_lemmas

variables {ι : Sort*} {α : Type*} {β : Type*} {f f₁ f₂ : α →. β}

lemma mem_dom_iff_dom (f : α →. β) (x : α) : x ∈ dom f ↔ (f x).dom :=
by simp [dom, set.mem_def]

lemma mem_dom_of_mem {f : α →. β} {x : α} {y : β} (h : y ∈ f x) : x ∈ dom f :=
(mem_dom f x).2 ⟨y, h⟩

lemma some_fn {f : α →. β} {x : α} (h : x ∈ f.dom) : roption.some (f.fn x h) = f x :=
roption.some_get h

lemma fn_mem {f : α →. β} {x : α} (h : x ∈ f.dom) : f.fn x h ∈ f x :=
roption.get_mem h

lemma mem_iff_fn_eq {x : α} {y : β} : y ∈ f x ↔ ∃ h : x ∈ f.dom, f.fn x h = y :=
by refl

lemma fn_eq_iff_mem {x : α} {y : β} (h : x ∈ f.dom) : f.fn x h = y ↔ y ∈ f x :=
by simp [mem_iff_fn_eq, h]

lemma fn_eq_of_mem {x : α} {y : β} (h1 : y ∈ f x) (h2 : x ∈ f.dom) : f.fn x h2 = y :=
(fn_eq_iff_mem h2).2 h1

/- more on lift -/

lemma mem_lift {f : α → β} {x : α} {y : β} : y ∈ (f : α →. β) x ↔ f x = y :=
by simp [eq_comm]

lemma lift_eq_some_iff {f : α → β} {x : α} {y : β} : (f : α →. β) x = roption.some y ↔ f x = y :=
by simp

@[simp] lemma fn_lift (f : α → β) (x : α) : (f : α →. β).fn x trivial = f x :=
by simp [fn_eq_iff_mem]

/-- The empty partial function -/
def empty : α →. β := λ x, roption.none

@[simp] lemma dom_empty : (empty : α →. β).dom = ∅ := rfl
@[simp] lemma empty_def (x : α) : (empty : α →. β) x = none := rfl
lemma not_mem_empty (x : α) (y : β) : y ∉ (pfun.empty : α →. β) x := roption.not_mem_none _

/- Two partial functions are equal if their graphs are equal -/
lemma ext_graph {α β : Type*} (f g : α →. β) (h_graph : f.graph = g.graph) : f = g :=
  pfun.ext $ λ _ _, iff_of_eq $ congr_fun h_graph (_,_)

lemma graph_empty_iff_dom_empty {α β : Type*} (f : α →. β) : f.graph = ∅ ↔ f.dom = ∅ :=
begin
  have := dom_iff_graph f,
  split; intro; ext; safe, exact this _ _ ‹_›
end

/-- A functional graph is a univalent graph -/
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
  cases this with this1 this2, rw [<-this2], convert this1, ext; refl
end

@[simp] lemma graph_of_graph {α β : Type*} (Γ : set $ α × β) (h_Γ : functional Γ) : (of_graph Γ h_Γ).graph = Γ :=
begin
  ext, rcases x with ⟨a,b⟩, dsimp[graph],
  split; intro H, {cases H, induction H_h, cases H_w, cases H_w_h, induction H_w_h_h,
  convert H_w_h_w, ext, refl, rw [of_graph_get], apply of_graph_val; try{assumption}; refl},
  fsplit, {tidy}, rw [of_graph_get], apply @of_graph_val _ _ Γ _ a _ (a,b) _;
  try{assumption}; refl
end

@[simp] lemma of_graph_graph {α β : Type*} {f : α →. β} : of_graph (f.graph) (graph_functional f) = f :=
  by apply ext_graph; rw [graph_of_graph]

@[simp] lemma dom_of_graph {α β : Type*} (Γ : set $ α × β) (h_Γ : functional Γ) : (of_graph Γ h_Γ).dom = (prod.fst '' Γ) :=
begin
 ext, split; intros, {tidy},
 {cases a, cases a_h, cases a_w, induction a_h_right, dsimp at *, fsplit,
 work_on_goal 0 { fsplit }, work_on_goal 2 {fsplit,
 work_on_goal 0 { assumption }, refl }}
end

@[simp] lemma dom_of_graph_union {α β : Type*} (Γ : set $ α × β) (p : α × β) (h_Γ : functional Γ) (h_Γ' : functional $ Γ ∪ {p}) : (of_graph (Γ ∪ {p}) h_Γ').dom = (of_graph Γ h_Γ).dom ∪ {p.fst} :=
  by simp[dom_of_graph, set.image_insert_eq]

lemma in_dom_of_in_graph {α β : Type*} {f : α →. β} : ∀ {a} {b}, (a,b) ∈ f.graph → a ∈ f.dom :=
  by {intros a b H, apply (pfun.dom_iff_graph _ a).mpr, exact ⟨b,H⟩}

lemma lift_graph' {α β : Type*} {f : α →. β} {a : α} {b : β} (h_a : a ∈ f.dom) : (a,b) ∈ f.graph ↔ pfun.fn f a h_a = b := by tidy

/-- The intersection of two partial functions -/
def inter (f₁ f₂ : α →. β) : α →. β :=
λ x, f₁ x ∩ f₂ x

instance : has_inter (α →. β) := ⟨pfun.inter⟩

@[simp] lemma mem_inter {x : α} {y : β} : y ∈ (f₁ ∩ f₂) x ↔ y ∈ f₁ x ∧ y ∈ f₂ x :=
roption.mem_inter

/-- f₁ is a subset, or subfunction of f₂: if `f₁ x = some y` then `f₂ x = some y` -/
def subfun (f₁ f₂ : α →. β) : Prop := ∀ x y, y ∈ f₁ x → y ∈ f₂ x

instance : partial_order (α →. β) :=
{ le := subfun,
  le_refl := λ f x y hy, hy,
  le_trans := λ f g h hfg hgh x y hy, hgh x y (hfg x y hy),
  le_antisymm := λ f g h1 h2, pfun.ext $ λ x y, ⟨h1 x y, h2 x y⟩ }

instance : semilattice_inf_bot (α →. β) :=
{ le := subfun,
  le_refl := λ f x y hy, hy,
  le_trans := λ f g h hfg hgh x y hy, hgh x y (hfg x y hy),
  le_antisymm := λ f g h1 h2, pfun.ext $ λ x y, ⟨h1 x y, h2 x y⟩,
  bot := pfun.empty,
  bot_le := λ f x y hy, false.elim $ roption.not_mem_none y hy,
  inf := pfun.inter,
  inf_le_left := λ f g x y hy, (mem_inter.1 hy).1,
  inf_le_right := λ f g x y hy, (mem_inter.1 hy).2,
  le_inf := λ f g h hfg hfh x y hf, mem_inter.2 ⟨hfg x y hf, hfh x y hf⟩ }

lemma le_def : f₁ ≤ f₂ ↔ ∀ x y, y ∈ f₁ x → y ∈ f₂ x := by refl

lemma dom_subset_dom_of_le (h : f₁ ≤ f₂) : f₁.dom ⊆ f₂.dom :=
λ x hx, mem_dom_of_mem (h x (f₁.fn x hx) (fn_mem hx))

lemma eq_some_of_subfun (h : f₁ ≤ f₂) {x : α} {y : β} (h1 : f₁ x = roption.some y) :
  f₂ x = roption.some y :=
by { rw [roption.eq_some_iff] at h1 ⊢, exact h x y h1 }

lemma fn_eq_of_subfun (h : f₁ ≤ f₂) {x : α} {y : β} (h1 : x ∈ f₁.dom)
  (h2 : f₁.fn x h1 = y) (h3 : x ∈ f₂.dom) : f₂.fn x h3 = y :=
by { apply fn_eq_of_mem, apply h, rw [mem_iff_fn_eq], exact ⟨h1, h2⟩ }

lemma le_lift {f : α →. β} {g : α → β} : f ≤ (g : α →. β) ↔ ∀ x y, y ∈ f x → g x = y :=
by simp [le_def, eq_comm]

/-- Two functions are compatible if they agree on the intersection of their domains. -/
def compatible (f₁ f₂ : α →. β) : Prop :=
∀(x : α), x ∈ f₁.dom → x ∈ f₂.dom → f₁ x = f₂ x

lemma compatible_def : compatible f₁ f₂ ↔ ∀(x : α), x ∈ f₁.dom → x ∈ f₂.dom → f₁ x = f₂ x :=
by refl

lemma mem_of_compatible (h : compatible f₁ f₂) {x : α} {y : β} (h1 : y ∈ f₁ x) (h2 : x ∈ f₂.dom) :
  y ∈ f₂ x :=
by { convert h1, symmetry, exact h x (mem_dom_of_mem h1) h2 }

@[refl] lemma compatible_refl : compatible f f := λ x h1x h2x, rfl

lemma compatible_comm : compatible f₁ f₂ ↔ compatible f₂ f₁ :=
by { simp [compatible_def, eq_comm, imp.swap] }

lemma compatible_of_le (h : f₁ ≤ f₂) : compatible f₁ f₂ :=
begin
  intros x h1x h2x, apply roption.ext, intro y, split; intro hy, exact h x y hy,
  have := h x (f₁.fn x h1x) (fn_mem h1x),
  convert fn_mem h1x,
  rw [← roption.some_inj, ← roption.eq_some_iff.2 hy, ← roption.eq_some_iff.2 this]
end

/-- The sup of two functions f₁ and f₂. Corresponds to the set-theoretic union of f₁ and f₂ as
  long as f₁ and f₂ are compatible. If they are not compatible, the values of f₁ are chosen when
  both functions are defined. We use classical logic, so that we can define a has_sup instance
  (otherwise we would need to assume that `f₁.dom` is decidable). -/
def sup (f₁ f₂ : α →. β) : α →. β :=
λ a, if a ∈ f₁.dom then f₁ a else f₂ a

instance : has_sup (α →. β) := ⟨pfun.sup⟩

@[simp] lemma sup_eq_of_mem {x : α} (h : x ∈ f₁.dom) : (f₁ ⊔ f₂) x = f₁ x :=
by { dsimp [pfun.lattice.has_sup, pfun.sup], simp [h] }

@[simp] lemma sup_eq_of_nmem {x : α} (h : x ∉ f₁.dom) : (f₁ ⊔ f₂) x = f₂ x :=
by { dsimp [pfun.lattice.has_sup, pfun.sup], simp [h] }

@[simp] lemma dom_sup (f₁ f₂ : α →. β) : (f₁ ⊔ f₂).dom = f₁.dom ∪ f₂.dom :=
by { ext x, by_cases hx : x ∈ f₁.dom; simp [mem_dom_iff_dom] at hx; simp [mem_dom_iff_dom, hx] }

lemma subset_dom_sup_left (f₁ f₂ : α →. β) : f₁.dom ⊆ (f₁ ⊔ f₂).dom := by simp
lemma subset_dom_sup_right (f₁ f₂ : α →. β) : f₂.dom ⊆ (f₁ ⊔ f₂).dom := by simp

lemma mem_sup {x : α} {y : β} : y ∈ (f₁ ⊔ f₂) x ↔ y ∈ f₁ x ∨ (y ∈ f₂ x ∧ x ∉ f₁.dom) :=
begin
  by_cases hx : x ∈ f₁.dom, { simp [hx] },
  have := hx, rw [mem_dom] at this, push_neg at this, simp [hx, this]
end

lemma mem_sup_of_compatible {x : α} {y : β} (h : compatible f₁ f₂) :
  y ∈ (f₁ ⊔ f₂) x ↔ y ∈ f₁ x ∨ y ∈ f₂ x :=
begin
  rw [mem_sup, or_and_iff_or, or_not_iff],
  intros hy hx, convert hy, exact h x hx (mem_dom_of_mem hy),
end

lemma sup_restrict_left {f₁ f₂ : α →. β} :
  (f₁ ⊔ f₂).restrict (subset_dom_sup_left f₁ f₂) = f₁ :=
begin
  apply pfun.ext, intros x y, simp [mem_sup, and_or_and_not],
  show y ∈ f₁ x → x ∈ dom f₁, rw [mem_dom], intro hy, exact ⟨y, hy⟩
end

lemma sup_restrict_right {f₁ f₂ : α →. β} (h : compatible f₁ f₂) :
  (f₁ ⊔ f₂).restrict (subset_dom_sup_right f₁ f₂) = f₂ :=
begin
  apply pfun.ext, intros x y, simp [mem_sup_of_compatible h],
  rw [and_or_iff_and.2, and_iff_self_left], apply mem_dom_of_mem,
  intros hx hy, convert hy, symmetry, exact h x (mem_dom_of_mem hy) hx
end

lemma le_sup_left (f₁ f₂ : α →. β) : f₁ ≤ f₁ ⊔ f₂ :=
by { intros x y hy, rw [mem_sup], exact or.inl hy }

lemma le_sup_right (h : compatible f₁ f₂) : f₂ ≤ f₁ ⊔ f₂ :=
by { intros x y hy, rw [mem_sup_of_compatible h], exact or.inr hy }

/-- The indexed sup of a family of partial functions. This corresponds to the set-theoretic union
  if the functions are pairwise compatible. Otherwise, the value of a function will be chosen using
  classical.some. -/
def Sup (f : ι → α →. β) : α →. β :=
λ x, if h : ∃ i, x ∈ dom (f i) then f (classical.some h) x else roption.none

-- TODO: define Sup instance

lemma Sup_helper {f : ι → α →. β} {x : α} :
  (∃i, x ∈ (f i).dom) ↔ (∃i, x ∈ (f i).dom ∧ Sup f x = f i x) :=
⟨λ h, ⟨classical.some h, classical.some_spec h, dif_pos h⟩, λ⟨i, h, _⟩, ⟨i, h⟩⟩

lemma Sup_helper2 {f : ι → α →. β} {x : α} :
  (∃i, x ∈ (f i).dom) ↔ (∃i (h : x ∈ (f i).dom), Sup f x = roption.some ((f i).fn x h)) :=
begin
  rw [Sup_helper], apply exists_congr, intro i,
  rw [← exists_prop], apply exists_congr, intro hi,
  apply eq_iff_eq_of_eq_right, rw [some_fn hi]
end

@[simp] lemma dom_Sup (f : ι → α →. β) : (Sup f).dom = set.Union (λ (i : ι), (f i).dom) :=
begin
  ext x, rw [set.mem_Union], by_cases hx : ∃i, x ∈ (f i).dom,
  { simp only [hx, iff_true], rw [Sup_helper2] at hx, rcases hx with ⟨i, hx, h⟩,
    rw [mem_dom_iff_dom, h], trivial },
  { simp only [hx, iff_false], rw [mem_dom_iff_dom], dsimp [Sup], rw [dif_neg hx], exact id }
end

lemma subset_dom_Sup (f : ι → α →. β) (i : ι) : (f i).dom ⊆ (Sup f).dom :=
by { rw [dom_Sup], apply set.subset_Union (λ i, (f i).dom) }

lemma Sup_eq_of_mem {f : ι → α →. β} {x : α} {i : ι} (hf : ∀i j, compatible (f i) (f j))
  (h : x ∈ (f i).dom) : Sup f x = f i x :=
begin
  have : ∃ i, x ∈ (f i).dom := ⟨i, h⟩, rw [Sup_helper] at this, rcases this with ⟨j, hj, h2j⟩,
  rw [h2j], exact hf j i x hj h
end

lemma Sup_eq_of_nmem {f : ι → α →. β} {x : α} (h : ∀ i, x ∉ (f i).dom) :
  Sup f x = roption.none :=
by { dsimp [pfun.Sup], simp [h] }

lemma mem_Sup {f : ι → α →. β} {x : α} {y : β} (hf : ∀i j, compatible (f i) (f j)) :
  y ∈ Sup f x ↔ ∃ i, y ∈ f i x :=
begin
  split,
  { intro hy, have := mem_dom_of_mem hy, rw [dom_Sup, set.mem_Union] at this,
    cases this with i hi, use i, rwa [Sup_eq_of_mem hf hi] at hy },
  { rintro ⟨i, hi⟩, rwa [Sup_eq_of_mem hf (mem_dom_of_mem hi)] }
end

lemma Sup_restrict {f : ι → α →. β} (hf : ∀i j, compatible (f i) (f j)) (i : ι) :
  (Sup f).restrict (subset_dom_Sup f i) = f i :=
begin
  apply pfun.ext, intros x y, simp [mem_Sup hf],
  split,
  { rintro ⟨hx, j, hj⟩, exact mem_of_compatible (hf j i) hj hx },
  { intro hy, exact ⟨mem_dom_of_mem hy, i, hy⟩ }
end

lemma le_Sup {f : ι → α →. β} (hf : ∀i j, compatible (f i) (f j)) (i : ι) : f i ≤ Sup f :=
by { intros x y hy, rw [mem_Sup hf], exact ⟨i, hy⟩ }

lemma fn_mem_ran {X Y} {f : X →. Y} {x : X} {Hx : x ∈ f.dom} :
  (fn f x Hx) ∈ f.ran :=
by use x; tidy

lemma mk_ran_le_mk_dom {α β : Type u} (f : α →. β) : # f.ran ≤ # f.dom :=
begin
  refine mk_le_of_surjective _,
  { exact λ ⟨x,H⟩, ⟨fn f x H, by apply fn_mem_ran⟩},
  { intros y, by_contra, push_neg at a,
  /- `tidy` says -/ cases y, cases y_property, cases y_property_h,
    induction y_property_h_h, simp at *, dsimp at *,
    specialize a ‹_› ‹_›, finish }
end

/-- A partial function with one element in its domain.
  Note, this is a component of `pequiv.single` in a newer version of mathlib
  -/
def singleton (x : α) (y : β) : α →. β :=
λ a, { dom := a = x, get := λ _, y }

@[simp] lemma fn_singleton {x x' : α} {y : β} (H_a : x' = x) :
  fn (singleton x y) x' H_a = y := by refl

@[simp] lemma mem_singleton {x x' : α} {y y' : β} :
  y' ∈ singleton x y x' ↔ x = x' ∧ y = y' :=
begin
  split,
  { intro h, rw [roption.mem_eq] at h, rcases h with ⟨h, rfl⟩, exact ⟨h.symm, rfl⟩ },
  { rintro ⟨rfl, rfl⟩, exact ⟨rfl, rfl⟩ }
end

@[simp] lemma singleton_eq_some {x : α} {y : β} : singleton x y x = roption.some y :=
by simp [roption.eq_some_iff]

@[simp] lemma dom_singleton {x : α} {y : β} : (singleton x y).dom = {x} :=
by { ext x', simp [singleton, mem_dom_iff_dom] }

lemma mk_dom_singleton {x : α} {y : β} : # (singleton x y).dom = 1 := by simp

end pfun_lemmas

end pfun

section collapse_poset


structure collapse_poset (X Y : Type u) (κ : cardinal.{u}) : Type u :=
(f        : X →. Y)
(Hc       : #f.dom < κ)

def collapse_poset.empty {α β : Type u} {κ : cardinal} (h : 0 < κ) : collapse_poset α β κ :=
{ f := pfun.empty,
  Hc := by simp [h] }

open pfun

variables {X Y : Type u} {κ : cardinal.{u}}

/- TODO: separate out the lemma `#f.ran ≤ #f.dom` -/
lemma collapse_poset.mk_ran_lt (p : collapse_poset X Y κ) : # p.f.ran < κ :=
lt_of_le_of_lt (mk_ran_le_mk_dom p.f) p.Hc

def collapse_poset.inter (p₁ p₂ : collapse_poset X Y κ) : collapse_poset X Y κ :=
{ f := p₁.f ⊓ p₂.f,
  Hc := lt_of_le_of_lt (mk_le_mk_of_subset $ dom_subset_dom_of_le inf_le_left) p₁.Hc }

-- @[simp] lemma dom_reduce {D : X → Prop} {D_get : Π x (H : D x), Y} :
--   pfun.dom (λ x, roption.mk (D x) (D_get x) : X →. Y) = D := rfl

-- @[simp] lemma fn_reduce {D : X → Prop} {D_get : Πx (H : D x), Y} {x} {H} : pfun.fn (λ x, roption.mk (D x) (D_get x) : X →. Y) x H = D_get x H := rfl

noncomputable def collapse_poset.union (p₁ p₂ : collapse_poset X Y κ) (h : omega ≤ κ) :
  collapse_poset X Y κ :=
{ f := p₁.f ⊔ p₂.f,
  Hc := by { rw [dom_sup],
             exact lt_of_le_of_lt cardinal.mk_union_le (cardinal.add_lt_of_lt h p₁.Hc p₂.Hc) } }

lemma exists_mem_compl_dom_of_unctbl (p : collapse_poset X Y κ) (H_card : κ ≤ #X) :
  ∃ x : X, x ∉ p.f.dom :=
exists_mem_compl_of_mk_lt_mk _ $ lt_of_lt_of_le p.Hc H_card

lemma exists_mem_compl_ran_of_unctbl (p : collapse_poset X Y κ) (H_card : κ ≤ #Y) :
  ∃ y : Y, y ∉ p.f.ran :=
exists_mem_compl_of_mk_lt_mk _ $ lt_of_lt_of_le (collapse_poset.mk_ran_lt p) H_card

def collapse_poset.principal_open (p : collapse_poset X Y κ) : set (X → Y) :=
{f | p.f ≤ (f : X →. Y)}

@[simp] lemma collapse_poset.principal_open_empty (h : 0 < κ) :
  collapse_poset.principal_open (collapse_poset.empty h : collapse_poset X Y κ) = set.univ :=
begin
  ext f, split; intro H,
  { trivial },
  { tidy }
end

lemma mem_principal_open_iff {p : collapse_poset X Y κ} {f : X → Y} :
  f ∈ collapse_poset.principal_open p ↔ ∀ x y, y ∈ p.f x → f x = y :=
le_lift

lemma mem_principal_open_iff' {p : collapse_poset X Y κ} {f : X → Y} :
  f ∈ collapse_poset.principal_open p ↔ ∀ (x : X) (H_x : x ∈ p.f.dom), f x = fn p.f x H_x :=
begin
  rw [mem_principal_open_iff], apply forall_congr, intro x,
  split,
  { intros H Hx, apply H, apply fn_mem },
  { intros H y hy, rw [H $ mem_dom_of_mem hy], apply fn_eq_of_mem hy }
end

lemma mem_compl_principal_open_iff {p : collapse_poset X Y κ} {f : X → Y} :
  f ∈ - collapse_poset.principal_open p ↔ ∃x (H_x : x ∈ p.f.dom), f x ≠ fn p.f x H_x :=
by { rw [set.mem_compl_iff, mem_principal_open_iff'], push_neg }

@[simp] lemma mem_ran_of_mem_dom {p : collapse_poset X Y κ} {f : X → Y} {x : X}
  (H : f ∈ collapse_poset.principal_open p) : x ∈ p.f.dom → f x ∈ p.f.ran :=
by { intro H_mem, rw [mem_principal_open_iff] at H,
     use x, rw [H x (p.f.fn x H_mem) (fn_mem _)], exact roption.get_mem H_mem }

def collapse_poset.Sup {ι} (p : ι → collapse_poset X Y κ) (h : #ι < (ord κ).cof)
  (hκ : cardinal.omega ≤ κ) : collapse_poset X Y κ :=
⟨Sup $ λ i, (p i).f,
  begin
    rw [dom_Sup], apply lt_of_le_of_lt (mk_Union_le _) _,
    apply mul_lt_of_lt hκ (lt_of_lt_of_le h (ordinal.cof_ord_le κ)),
    exact ordinal.sup_lt _ h (λ i, collapse_poset.Hc _)
  end⟩

def collapse_space : topological_space (X → Y) :=
generate_from $
  (collapse_poset.principal_open : collapse_poset X Y cardinal.omega.succ → set (X → Y)) '' set.univ

local attribute [instance, priority 9001, reducible] collapse_space

@[simp] lemma collapse_poset.principal_open_is_open {p : collapse_poset X Y cardinal.omega.succ} :
  is_open (collapse_poset.principal_open p) :=
generate_open.basic _ $ set.mem_image_of_mem _ trivial

lemma one_lt_omega_succ : 1 < cardinal.omega.succ :=
lt_trans one_lt_omega (cardinal.lt_succ_self _)

lemma zero_lt_omega_succ : 0 < cardinal.omega.succ :=
lt_trans cardinal.zero_lt_one one_lt_omega_succ

open collapse_poset

def singleton_collapse_poset (x : X) (y : Y) (hκ : 1 < κ) : collapse_poset X Y κ :=
{ f := singleton x y,
  Hc := by simp [hκ] }

@[simp] lemma singleton_collapse_poset_principal_open {x : X} {y : Y} {hκ : 1 < κ} :
  principal_open (singleton_collapse_poset x y hκ) = {g : X → Y | g x = y} :=
begin
/- `tidy` says -/ ext1, cases hκ, induction κ, work_on_goal 0 { dsimp at *, fsplit, work_on_goal 0 { intros a }, work_on_goal 1 { intros a x_2 y_1 a_1, cases a_1, induction a, induction a_1_h, induction a_1_w, dsimp at *, simp at *, refl } }, work_on_goal 1 { refl },
  rw [←lift_eq_some_iff], apply eq_some_of_subfun a, simp [singleton_collapse_poset]
end

lemma collapse_poset.compl_principal_open_is_Union (hκ : 1 < κ) (p : collapse_poset X Y κ) :
  ∃ {ι : Type u} (s : ι → collapse_poset X Y κ),
    set.Union (λ i : ι, principal_open $ s i) = - principal_open p :=
begin
  use {pr : X × Y // ∃ H_mem : pr.1 ∈ p.f.dom, pr.2 ≠ fn p.f pr.1 H_mem },
  use (λ s, singleton_collapse_poset s.1.1 s.1.2 hκ),
  ext f, split; intro H,
    { intro H_mem,
      rcases H with ⟨P, ⟨⟨⟨x',y'⟩, ⟨H_mem₁, H_neq⟩⟩, rfl⟩, H_mem₂⟩,
      dsimp at H_neq H_mem₂,
      apply H_neq,
      rw [← show f x' = y', by simpa using H_mem₂],
      rw mem_principal_open_iff'.mp H_mem _ _ },
    { rw [mem_compl_principal_open_iff] at H, rcases H with ⟨x, Hx, H_neq⟩,
      suffices this : ∃ (a : X) (H_mem : (a, f a).fst ∈ dom (p.f)), ¬f a = fn (p.f) a H_mem,
      { simp [this] },
      exact ⟨_, by use ‹_›⟩ }
end

@[simp] lemma collapse_poset.principal_open_is_closed {p : collapse_poset X Y cardinal.omega.succ} :
  is_closed (collapse_poset.principal_open p) :=
by { rcases collapse_poset.compl_principal_open_is_Union one_lt_omega_succ p with ⟨ι, ⟨s, Hu⟩⟩,
     rw [is_closed, ← Hu], simp [is_open_Union] }

@[simp] lemma collapse_poset.is_regular_principal_open
  (p : collapse_poset X Y cardinal.omega.succ) : is_regular (collapse_poset.principal_open p) :=
by simp [is_clopen]

lemma inter_principal_open (hκ : omega ≤ κ) {p₁ p₂ : collapse_poset X Y κ}
  (H : compatible p₁.f p₂.f) :
  principal_open p₁ ∩ principal_open p₂ = principal_open (p₁.union p₂ hκ) :=
begin
  ext f,
  simp [mem_principal_open_iff],
  rw [← forall_and_distrib], apply forall_congr, intro x,
  rw [← forall_and_distrib], apply forall_congr, intro y,
  rw [union, mem_sup_of_compatible H, or_imp_distrib]
end

def collapse_space_basis : set $ set (X → Y) :=
insert (∅ : set (X → Y))
  (collapse_poset.principal_open '' (set.univ : set (collapse_poset X Y cardinal.omega.succ)))

def collapse_space_basis_spec : @is_topological_basis (X → Y) collapse_space collapse_space_basis :=
begin
  refine ⟨λ P HP P' HP' f H_mem_inter, _,_,_⟩,
    { rw [collapse_space_basis] at HP HP',
      cases HP; cases HP',

      { suffices this : f ∈ (∅ : set $ X → Y),
          by {cases this}, substs HP, cases H_mem_inter, exact ‹_› },
      { suffices this : f ∈ (∅ : set $ X → Y),
          by {cases this}, substs HP, cases H_mem_inter, exact ‹_› },
      { suffices this : f ∈ (∅ : set $ X → Y),
          by {cases this}, substs HP', cases H_mem_inter, exact ‹_› },

      simp only [set.image_univ, set.mem_range] at HP HP',
      cases HP with y Hy; cases HP' with y' Hy',

      substs Hy Hy', use (principal_open y ∩ principal_open y'),
      refine ⟨_,⟨‹_›,(by refl)⟩⟩,
      { by_cases H_compat : compatible y.f y'.f,
        { right, refine ⟨_,⟨trivial, _⟩⟩, exact y.union y' (le_of_lt (lt_succ_self _)),
        rwa [inter_principal_open] },
        { suffices this : principal_open y ∩ principal_open y' = ∅,
            by {rw [this], exact or.inl rfl },
          ext g; split; intro H,
            { exfalso, cases H with H₁ H₂, rw [mem_principal_open_iff] at H₁ H₂,
              rw [compatible] at H_compat,
              push_neg at H_compat, rcases H_compat with ⟨x, Hx₁, Hx₂, Hx₃⟩,
              apply Hx₃, rw [← some_fn Hx₁, ← some_fn Hx₂],
              rw [← H₁ x _ (fn_mem Hx₁), ← H₂ x _ (fn_mem Hx₂)] },
            { cases H }}}},

    { refine le_antisymm (λ _ _, trivial) _,
      intros f _a, refine ⟨_,_⟩,
      { exact (principal_open (collapse_poset.empty zero_lt_omega_succ)) },
      { refine ⟨by {rw [collapse_space_basis], right, exact set.mem_image_univ},_⟩, simp }},
    { unfold collapse_space_basis collapse_space, refine le_antisymm _ _,
      { refine generate_from_mono _, exact λ _ _, or.inr ‹_›},
      { intros T HT, induction HT,
        { cases HT_H, subst HT_H, exact is_open_empty, constructor, exact ‹_› },
        { exact is_open_univ },
        { apply generate_open.inter, exact ‹_›, exact ‹_› },
        { apply generate_open.sUnion, intros S HS, solve_by_elim }}}
end

@[simp] lemma is_regular_singleton_regular_open {x : X} {y : Y} :
  is_regular (principal_open (singleton_collapse_poset x y one_lt_omega_succ)) :=
collapse_poset.is_regular_principal_open _

@[simp] lemma is_regular_singleton_regular_open' {x : X} {y : Y} :
  is_regular {g : X → Y | g x = y} :=
by {rw [<-singleton_collapse_poset_principal_open], exact is_regular_singleton_regular_open}

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

lemma trivial_extension_mem_principal_open {p : collapse_poset X Y κ} {y : Y}
  : (trivial_extension p.f y) ∈ collapse_poset.principal_open p :=
by { simp [trivial_extension, mem_principal_open_iff],
     intros x y hy, simp [mem_dom_of_mem hy, fn_eq_of_mem hy] }

end collapse_poset

section omega_closed_dense_subset

variables {α : Type*} [nontrivial_complete_boolean_algebra α]

-- any ω-indexed downward chain in D has an intersection in D
def omega_closed (D : set α) : Prop :=
∀ (s : ℕ → α) (s_sub_D : ∀n, s n ∈ D) (H_nonzero : ∀ n, ⊥ < s n) (H_chain : ∀ n, s (n+1) ≤ s n), (⨅n, s n) ∈ D

def dense_subset {α : Type*} [order_bot α] (D : set α) : Prop :=
⊥ ∉ D ∧ ∀x, ⊥ < x → ∃ y ∈ D, y < x

@[reducible]def dense_omega_closed_subset (D : set α) : Prop :=
dense_subset D ∧ omega_closed D

variable (α)
def has_dense_omega_closed_subset : Prop :=
∃ D : set α, dense_omega_closed_subset D

variable {α}

lemma nonzero_of_mem_dense_omega_closed_subset {x : α} {D : set α} (H : dense_omega_closed_subset D) (H_mem : x ∈ D) : ⊥ < x :=
by {have := H.left.left, by_contra H', finish [le_bot_iff_not_bot_lt]}

lemma nonzero_infi_of_mem_dense_omega_closed_subset {s : ℕ → α} {D : set α} (H : dense_omega_closed_subset D) (H_chain : ∀ n, s (n + 1) ≤ s n) (H_mem : ∀ n, s n ∈ D) : ⊥ < ⨅ n, s n :=
begin
  apply nonzero_of_mem_dense_omega_closed_subset H, refine H.right s ‹_› _ ‹_›,
  intro n, specialize H_mem n, from nonzero_of_mem_dense_omega_closed_subset H ‹_›
end

end omega_closed_dense_subset


local attribute [instance, priority 9000] collapse_space

section collapse_algebra
variables X Y : Type u

def collapse_algebra : Type* := @regular_opens (X → Y) collapse_space

variables {X Y}

@[instance, priority 9001] def collapse_algebra_boolean_algebra [nonempty (X → Y)] : nontrivial_complete_boolean_algebra (collapse_algebra X Y) :=
regular_open_algebra

end collapse_algebra

section collapse_poset_dense
variables {X Y : Type u}

def collapse_poset.inclusion (p : collapse_poset X Y cardinal.omega.succ) :
  collapse_algebra X Y :=
⟨collapse_poset.principal_open p, collapse_poset.is_regular_principal_open p⟩

local notation `ι`:65 := collapse_poset.inclusion

lemma collapse_poset_dense_basis : ∀ T ∈ @collapse_space_basis X Y,
  ∀ h_nonempty : T ≠ ∅, ∃ p : collapse_poset X Y cardinal.omega.succ, (ι p).val ⊆ T :=
begin
  intros T H_mem_basis _,
  refine or.elim H_mem_basis (λ _, (false.elim (absurd ‹T = ∅› ‹_›))) (λ H, _),
  rcases H with ⟨_,⟨_,H₂⟩⟩, exact ⟨‹_›, by simp[H₂, collapse_poset.inclusion]⟩
end

lemma collapse_poset_dense [nonempty (X → Y)] {b : collapse_algebra X Y}
  (H : ⊥ < b) : ∃ p : (collapse_poset X Y cardinal.omega.succ), ι p ≤ b :=
begin
  cases (classical.choice (classical.nonempty_of_not_empty _ H.right.symm)) with S_wit H_wit,
  change ∃ p, (ι p).val ⊆ b.val,
  have := mem_basis_subset_of_mem_open (collapse_space_basis_spec) H_wit (is_open_of_is_regular b.property),
  rcases (mem_basis_subset_of_mem_open
           (collapse_space_basis_spec) H_wit (is_open_of_is_regular b.property))
         with ⟨v, Hv₁, Hv₂, Hv₃⟩,
  have : v ≠ ∅, by {intro H, rw [H] at Hv₂, cases Hv₂},
  cases (collapse_poset_dense_basis ‹_› ‹_› ‹_›) with p H_p, exact ⟨p, set.subset.trans H_p ‹_›⟩
end

lemma principal_opens_dense_omega_closed [nonempty $ X → Y] : @dense_omega_closed_subset _ (collapse_algebra_boolean_algebra) (set.range ι : set $ collapse_algebra X Y) :=
sorry

end collapse_poset_dense

local notation `𝔹` := collapse_algebra ((ℵ₁ : pSet).type) (powerset omega : pSet).type

instance nonempty_aleph_one_powerset_omega : nonempty $ ((ℵ₁).type) → (powerset omega).type :=
⟨λ _, by {unfold pSet.omega, exact λ _, false}⟩

def collapse_boolean_algebra : nontrivial_complete_boolean_algebra 𝔹 :=
by apply_instance


