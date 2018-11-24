import .fol

open set function
universe variable u
namespace fol

namespace Language
protected def sum (L L' : Language) : Language :=
⟨λn, L.functions n ⊕ L'.functions n, λ n, L.relations n ⊕ L'.relations n⟩

def symbols (L : Language) := (Σl, L.functions l) ⊕ (Σl, L.relations l)
end Language

section
variable {L : Language}
def symbols_in_term : ∀{l}, preterm L l → set L.symbols
| _ &k          := ∅
| l (func f)    := {sum.inl ⟨l,f⟩}
| _ (app t₁ t₂) := symbols_in_term t₁ ∪ symbols_in_term t₂

def symbols_in_formula : ∀{l}, preformula L l → set L.symbols
| _ falsum       := ∅
| _ (t₁ ≃ t₂)    := symbols_in_term t₁ ∪ symbols_in_term t₂
| l (rel R)      := {sum.inr ⟨l, R⟩}
| _ (apprel f t) := symbols_in_formula f ∪ symbols_in_term t
| _ (f₁ ⟹ f₂)   := symbols_in_formula f₁ ∪ symbols_in_formula f₂
| _ (∀' f)       := symbols_in_formula f

def symbols_in_prf : ∀{Γ : set $ formula L} {f : formula L} (P : Γ ⊢ f), set L.symbols
| Γ f (axm h)              := symbols_in_formula f
| Γ (f₁ ⟹ f₂) (impI P)    := symbols_in_prf P ∪ symbols_in_formula f₁
| Γ f₂ (impE f₁ P₁ P₂)     := symbols_in_prf P₁ ∪ symbols_in_prf P₂
| Γ f (falsumE P)          := symbols_in_prf P ∪ symbols_in_formula f
| Γ (∀' f) (allI P)        := symbols_in_prf P
| Γ _ (allE₂ f t P)        := symbols_in_prf P ∪ symbols_in_term t
| Γ (_ ≃ t) (ref _ _)     := symbols_in_term t
| Γ _ (subst₂ s t f P₁ P₂) := symbols_in_prf P₁ ∪ symbols_in_prf P₂

def interpolation : ∀{Γ : set $ formula L} {f : formula L} (P : Γ ⊢ f), 
  Σ' (f' : formula L) (P₁ : Γ ⊢ f') (P₂ : {f'} ⊢ f), 
    symbols_in_prf P₁ ⊆ ⋃₀ (symbols_in_formula '' Γ) ∧ 
    symbols_in_prf P₂ ⊆ symbols_in_formula f ∧ 
    symbols_in_formula f' ⊆ ⋃₀ (symbols_in_formula '' Γ) ∩ symbols_in_formula f := 
sorry -- probably the last property follows automatically

end

structure Lhom (L L' : Language) :=
(on_function : ∀{n}, L.functions n → L'.functions n) 
(on_relation : ∀{n}, L.relations n → L'.relations n)

local infix ` →ᴸ `:10 := Lhom -- \^L

namespace Lhom
/- -/
variables {L : Language.{u}} {L' : Language.{u}} (ϕ : L →ᴸ L')

protected def id (L : Language) : L →ᴸ L :=
⟨λn, id, λ n, id⟩

structure is_injective : Prop := 
(on_function {n} : injective (on_function ϕ : L.functions n → L'.functions n))
(on_relation {n} : injective (on_relation ϕ : L.relations n → L'.relations n))

@[simp] def on_term : ∀{l}, preterm L l → preterm L' l
| _ &k          := &k
| _ (func f)    := func $ ϕ.on_function f
| _ (app t₁ t₂) := app (on_term t₁) (on_term t₂)

@[simp] lemma on_term_lift_at : ∀{l} (t : preterm L l) (n m : ℕ), 
  ϕ.on_term (t ↑' n # m) = ϕ.on_term t ↑' n # m
| _ &k          n m := by by_cases h : m ≤ k; simp [h]
| _ (func f)    n m := by refl
| _ (app t₁ t₂) n m := by simp*

@[simp] lemma on_term_lift {l} (n : ℕ) (t : preterm L l) : ϕ.on_term (t ↑ n) = ϕ.on_term t ↑ n :=
ϕ.on_term_lift_at t n 0

@[simp] lemma on_term_subst : ∀{l} (t : preterm L l) (s : term L) (n : ℕ), 
  ϕ.on_term (t[s // n]) = ϕ.on_term t[ϕ.on_term s // n]
| _ &k          s n := by apply lt_by_cases k n; intro h; simp [h]
| _ (func f)    s n := by refl
| _ (app t₁ t₂) s n := by simp*

@[simp] def on_formula : ∀{l}, preformula L l → preformula L' l
| _ falsum       := falsum
| _ (t₁ ≃ t₂)    := ϕ.on_term t₁ ≃ ϕ.on_term t₂
| _ (rel R)      := rel $ ϕ.on_relation R
| _ (apprel f t) := apprel (on_formula f) $ ϕ.on_term t
| _ (f₁ ⟹ f₂)   := on_formula f₁ ⟹ on_formula f₂
| _ (∀' f)       := ∀' on_formula f

@[simp] lemma on_formula_lift_at : ∀{l} (n m : ℕ) (f : preformula L l), 
  ϕ.on_formula (f ↑' n # m) = ϕ.on_formula f ↑' n # m
| _ n m falsum       := by refl
| _ n m (t₁ ≃ t₂)    := by simp
| _ n m (rel R)      := by refl
| _ n m (apprel f t) := by simp*
| _ n m (f₁ ⟹ f₂)   := by simp*
| _ n m (∀' f)       := by simp*

@[simp] lemma on_formula_lift {l} (n : ℕ) (f : preformula L l) : 
  ϕ.on_formula (f ↑ n) = ϕ.on_formula f ↑ n :=
ϕ.on_formula_lift_at n 0 f

@[simp] lemma on_formula_subst : ∀{l} (f : preformula L l) (s : term L) (n : ℕ), 
  ϕ.on_formula (f[s // n]) = ϕ.on_formula f[ϕ.on_term s // n]
| _ falsum       s n := by refl
| _ (t₁ ≃ t₂)    s n := by simp
| _ (rel R)      s n := by refl
| _ (apprel f t) s n := by simp*
| _ (f₁ ⟹ f₂)   s n := by simp*
| _ (∀' f)       s n := by simp*

def on_bounded_term {n} : ∀{l} (t : bounded_preterm L n l), bounded_preterm L' n l
| _ &k           := &k
| _ (bd_func f)  := bd_func $ ϕ.on_function f
| _ (bd_app t s) := bd_app (on_bounded_term t) (on_bounded_term s)

def on_bounded_formula : ∀{n l} (f : bounded_preformula L n l), bounded_preformula L' n l
| _ _ bd_falsum       := ⊥
| _ _ (t₁ ≃ t₂)       := ϕ.on_bounded_term t₁ ≃ ϕ.on_bounded_term t₂
| _ _ (bd_rel R)      := bd_rel $ ϕ.on_relation R
| _ _ (bd_apprel f t) := bd_apprel (on_bounded_formula f) $ ϕ.on_bounded_term t
| _ _ (f₁ ⟹ f₂)      := on_bounded_formula f₁ ⟹ on_bounded_formula f₂
| _ _ (∀' f)          := ∀' on_bounded_formula f

def on_closed_term (t : closed_term L) : closed_term L' := ϕ.on_bounded_term t
def on_sentence (f : sentence L) : sentence L' := ϕ.on_bounded_formula f

def on_prf {Γ : set $ formula L} {f : formula L} (h : Γ ⊢ f) : ϕ.on_formula '' Γ ⊢ ϕ.on_formula f :=
begin
  induction h,
  { apply axm, exact mem_image_of_mem _ h_h, },
  { apply impI, rw [←image_insert_eq], exact h_ih },
  { exact impE _ h_ih_h₁ h_ih_h₂, },
  { apply falsumE, rw [image_insert_eq] at h_ih, exact h_ih },
  { apply allI, rw [←image_comp] at h_ih ⊢, simp [image_congr' (on_formula_lift ϕ 1)] at h_ih, 
    exact h_ih },
  { apply allE _ _ h_ih, symmetry, apply on_formula_subst },
  { apply prf.ref },
  { simp at h_ih_h₂, apply subst _ h_ih_h₁ h_ih_h₂, simp }
end

variable {ϕ}
lemma on_term_inj (h : ϕ.is_injective) {l} : injective (ϕ.on_term : preterm L l → preterm L' l) :=
begin
  intros x y hxy, induction x generalizing y; cases y; try {injection hxy with hxy' hxy''},
  { rw [hxy'] },
  { rw [h.on_function hxy'] },
  { congr1, exact x_ih_t hxy', exact x_ih_s hxy'' }
end

lemma on_formula_inj (h : ϕ.is_injective) {l} : 
  injective (ϕ.on_formula : preformula L l → preformula L' l) :=
begin
  intros x y hxy, induction x generalizing y; cases y; try {injection hxy with hxy' hxy''},
  { refl },
  { rw [on_term_inj h hxy', on_term_inj h hxy''] },
  { rw [h.on_relation hxy'] },
  { rw [x_ih hxy', on_term_inj h hxy''] },
  { rw [x_ih_f₁ hxy', x_ih_f₂ hxy''] },
  { rw [x_ih hxy'] }
end

def refect_prf {Γ : set $ formula L} {f : formula L} (hϕ : ϕ.is_injective) : 
  ϕ.on_formula '' Γ ⊢ ϕ.on_formula f → Γ ⊢ f :=
begin
  have : ∀(Δ : set $ formula L') (g : formula L'), 
    ϕ.on_formula '' Γ = Δ → ϕ.on_formula f = g → Δ ⊢ g → Γ ⊢ f,
  intros Δ g hΓ hf h,
  induction h generalizing Γ f; try {subst hΓ}; try {subst hf},
  { apply axm, exact (mem_image_of_injective $ on_formula_inj hϕ).mp h_h, },
  { cases f; cases hf, apply impI, apply h_ih, rw [image_insert_eq], refl },
  { sorry }, -- we need something like a reduced proof tree here.
  { sorry },
  { sorry },
  { sorry },
  { cases f; injection hf with hf₁ hf₂, subst hf₂, cases on_term_inj hϕ hf₁, apply prf.ref },
  { sorry }, 
  exact this _ _ rfl rfl
end

variable (ϕ)

/-- Given L → L' and an L'-structure S, the reduct of S to L is the L-structure given by
restricting interpretations from L' to L --/
def reduct (S : Structure L') : Structure L :=
have x : Type*, from S.carrier,
⟨ S.carrier, λn f, S.fun_map $ ϕ.on_function f, λn R, S.rel_map $ ϕ.on_relation R⟩ 

variable {ϕ}

def reduct_id {S : Structure L'} : S → reduct ϕ S := id

def reduct_ssatisfied {S : Structure L'} {f : sentence L} (h : S ⊨ ϕ.on_sentence f) :
  ϕ.reduct S ⊨ f :=
begin
  rcases f,
  {exact h},
  {unfold on_sentence on_bounded_formula on_bounded_term realize_sentence realize_bounded_formula at h, unfold realize_sentence realize_bounded_formula realize_bounded_term,
  fapply @eq.rec, fapply @reduct_id L L' ϕ, exact realize_bounded_term dvector.nil (on_bounded_term ϕ f_t₁) dvector.nil, unfold reduct_id, rcases f_t₁, repeat{sorry},
  -- seems like here we need to show that induced interpretation on terms is literally equal to the reduct interpretation
  },
  {sorry},
  {sorry},
  {sorry},
  {sorry},
end

def reduct_all_ssatisfied {S : Structure L'} {T : Theory L} (h : S ⊨ ϕ.on_sentence '' T) :
  ϕ.reduct S ⊨ T :=
λf hf, reduct_ssatisfied $ h $ mem_image_of_mem _ hf

lemma reduct_nonempty_of_nonempty {S : Structure L'} (H : nonempty S) : nonempty (reduct ϕ S) :=
by {apply nonempty.map, repeat{assumption}, exact reduct_id}

end Lhom


def Theory_induced {L L' : Language} (F : L →ᴸ L') (T : Theory L) : Theory L' :=
  (Lhom.on_sentence F) '' T

lemma consis_Theory_induced_of_consis {L L' : Language} (F : L →ᴸ L') (T : Theory L) {hT : is_consistent T} : is_consistent (Theory_induced F T) := sorry

end fol




-- instance nonempty_Language_over : nonempty (Language_over) :=
--   begin fapply nonempty.intro, exact ⟨L, language_id_morphism L⟩ end

--TODO define map induced by a language_morphism on terms/preterms, formulas/preformulas, sets of formulas/theories
