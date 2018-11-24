import .fol

open set function
universe variable u
namespace fol

local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`:0) := l


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


@[reducible]def comp {L1} {L2} {L3} (g : L2 →ᴸ L3) (f : L1 →ᴸ L2) : L1 →ᴸ L3 :=
begin
--  rcases g with ⟨g1, g2⟩, rcases f with ⟨f1,f2⟩,
--  exact ⟨λn, g1 ∘ f1, λn, g2 ∘ f2⟩
split, 
  all_goals{intro n},
  let g1 := g.on_function, let f1 := f.on_function,-- Lean's not letting me "@" g.on_function etc
    exact (@g1 n) ∘ (@f1 n),
  let g2 := g.on_relation, let f2 := f.on_relation,
    exact (@g2 n) ∘ (@f2 n)
end

local infix ` ∘ `:60 := Lhom.comp

lemma id_is_left_identity {L1 L2} {F : L1 →ᴸ L2} : (Lhom.id L2) ∘ F = F := by {cases F, refl}

lemma id_is_right_identity {L1 L2} {F : L1 →ᴸ L2} : F ∘ (Lhom.id L1) = F := by {cases F, refl}

structure is_injective : Prop := 
(on_function {n} : injective (on_function ϕ : L.functions n → L'.functions n))
(on_relation {n} : injective (on_relation ϕ : L.relations n → L'.relations n))

class has_decidable_range : Type u := 
(on_function {n} : decidable_pred (range (on_function ϕ : L.functions n → L'.functions n)))
(on_relation {n} : decidable_pred (range (on_relation ϕ : L.relations n → L'.relations n)))

attribute [instance] has_decidable_range.on_function has_decidable_range.on_relation

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

@[simp] def on_term_apps : ∀{l} (t : preterm L l) (ts : dvector (term L) l),
  ϕ.on_term (apps t ts) = apps (ϕ.on_term t) (ts.map ϕ.on_term)
| _ t []       := by refl
| _ t (t'::ts) := by simp*

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

@[simp] def on_bounded_term {n} : ∀{l} (t : bounded_preterm L n l), bounded_preterm L' n l
| _ &k           := &k
| _ (bd_func f)  := bd_func $ ϕ.on_function f
| _ (bd_app t s) := bd_app (on_bounded_term t) (on_bounded_term s)

@[simp] def on_bounded_term_fst {n} : ∀{l} (t : bounded_preterm L n l), 
  (ϕ.on_bounded_term t).fst = ϕ.on_term t.fst
| _ &k           := by refl
| _ (bd_func f)  := by refl
| _ (bd_app t s) := by dsimp; simp*

@[simp] def on_bounded_formula : ∀{n l} (f : bounded_preformula L n l), bounded_preformula L' n l
| _ _ bd_falsum       := ⊥
| _ _ (t₁ ≃ t₂)       := ϕ.on_bounded_term t₁ ≃ ϕ.on_bounded_term t₂
| _ _ (bd_rel R)      := bd_rel $ ϕ.on_relation R
| _ _ (bd_apprel f t) := bd_apprel (on_bounded_formula f) $ ϕ.on_bounded_term t
| _ _ (f₁ ⟹ f₂)      := on_bounded_formula f₁ ⟹ on_bounded_formula f₂
| _ _ (∀' f)          := ∀' on_bounded_formula f

@[simp] def on_bounded_formula_fst : ∀{n l} (f : bounded_preformula L n l), 
  (ϕ.on_bounded_formula f).fst = ϕ.on_formula f.fst
| _ _ bd_falsum       := by refl
| _ _ (t₁ ≃ t₂)       := by simp
| _ _ (bd_rel R)      := by refl
| _ _ (bd_apprel f t) := by simp*
| _ _ (f₁ ⟹ f₂)      := by simp*
| _ _ (∀' f)          := by simp*

@[simp] def on_closed_term (t : closed_term L) : closed_term L' := ϕ.on_bounded_term t
@[simp] def on_sentence (f : sentence L) : sentence L' := ϕ.on_bounded_formula f

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

def on_sprf {Γ : set $ sentence L} {f : sentence L} (h : Γ ⊢ f) : 
  ϕ.on_sentence '' Γ ⊢ ϕ.on_sentence f :=
by simp only [sprf, Theory.fst, (image_comp bounded_preformula.fst _ _).symm, comp, 
  on_bounded_formula_fst, image_comp ϕ.on_formula bounded_preformula.fst, on_sentence]; 
  exact ϕ.on_prf h

/- replace all symbols not in the image of ϕ by a new variable -/
noncomputable def reflect_term [has_decidable_range ϕ] (t : term L') (m : ℕ) : term L :=
term.elim (λk, &k ↑' 1 # m) 
     (λl f' xs' xs, if hf' : f' ∈ range (@on_function _ _ ϕ l)
       then apps (func (classical.some hf')) xs else &0) t

lemma reflect_term_on_term [has_decidable_range ϕ] (t : term L) (m : ℕ) : 
  ϕ.reflect_term (ϕ.on_term t) m = t ↑' 1 # m :=
sorry

noncomputable def reflect_formula [has_decidable_range ϕ] (f : formula L') : 
  ∀(m : ℕ), formula L :=
formula.rec (λm, ⊥) (λt₁ t₂ m, ϕ.reflect_term t₁ m ≃ ϕ.reflect_term t₂ m)
  (λl R' xs' m, if hR' : R' ∈ range (@on_relation _ _ ϕ l)
       then apps_rel (rel (classical.some hR')) (xs'.map $ λt, ϕ.reflect_term t m) else ⊤)
   (λf₁' f₂' f₁ f₂ m, f₁ m ⟹ f₂ m) (λf' f m, ∀' f (m+1)) f

lemma reflect_formula_on_formula [has_decidable_range ϕ] (f : formula L) (m : ℕ) : 
  ϕ.reflect_formula (ϕ.on_formula f) m = f ↑' 1 # m :=
sorry

noncomputable def reflect_prf_gen [has_decidable_range ϕ] {Γ} {f : formula L'} (m) (H : Γ ⊢ f) : 
  (λf, ϕ.reflect_formula f m) '' Γ ⊢ ϕ.reflect_formula f m :=
begin
  induction H generalizing m,
  { apply axm, apply mem_image_of_mem _ H_h },
  { apply impI, have h := @H_ih m, rw [image_insert_eq] at h, exact h },
  { apply impE, apply H_ih_h₁, apply H_ih_h₂ },
  { apply falsumE, have h := @H_ih m, rw [image_insert_eq] at h, exact h },
  { apply allI, rw [←image_comp], have h := @H_ih (m+1), rw [←image_comp] at h, 
    apply cast _ h, congr1, apply image_congr', intro, sorry },
  { sorry /-apply allE _ _ _, symmetry, sorry, sorry-/ },
  { apply ref },
  { sorry 
  -- apply subst _ H_ih_h₁, { have h := @H_ih_h₂ m, /-rw [subst_formula2_zero] at h, exact h-/ sorry }, sorry, sorry
    /-rw [subst_formula2_zero]-/ },
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

def of_prf_lift {Γ} {f : formula L} (n m : ℕ) 
  (H : (λf' : formula L, f' ↑' n # m) '' Γ ⊢ f ↑' n # m) : Γ ⊢ f :=
begin
  sorry
end

noncomputable def reflect_prf {Γ : set $ formula L} {f : formula L} (hϕ : ϕ.is_injective)
  (h : ϕ.on_formula '' Γ ⊢ ϕ.on_formula f) : Γ ⊢ f :=
begin
  haveI : has_decidable_range ϕ :=
    ⟨λl f, classical.prop_decidable _, λl R, classical.prop_decidable _⟩ ,
  apply of_prf_lift 1 0,
  rw [(reflect_formula_on_formula ϕ f 0).symm],
  refine eq.mp _ (ϕ.reflect_prf_gen 0 h),
  rw [funext (λf, (reflect_formula_on_formula ϕ f 0).symm), ←image_comp]
end

variable (ϕ)

/-- Given L → L' and an L'-structure S, the reduct of S to L is the L-structure given by
restricting interpretations from L' to L --/
def reduct (S : Structure L') : Structure L :=
have x : Type*, from S.carrier,
⟨ S.carrier, λn f, S.fun_map $ ϕ.on_function f, λn R, S.rel_map $ ϕ.on_relation R⟩ 

variable {ϕ}

def reduct_id {S : Structure L'} : S → reduct ϕ S := id

def reduct_ssatisfied {S : Structure L'} {f : sentence L} (hϕ : ϕ.is_injective) 
  (h : S ⊨ ϕ.on_sentence f) : ϕ.reduct S ⊨ f :=
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

def reduct_all_ssatisfied {S : Structure L'} {T : Theory L} (hϕ : ϕ.is_injective) 
  (h : S ⊨ ϕ.on_sentence '' T) : ϕ.reduct S ⊨ T :=
λf hf, reduct_ssatisfied hϕ $ h $ mem_image_of_mem _ hf

def reduct_ssatisfied' {T : Theory L} (f : sentence L) (h : T ⊨ f) :
  ϕ.on_sentence '' T ⊨ ϕ.on_sentence f :=
λS hS h, sorry

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
