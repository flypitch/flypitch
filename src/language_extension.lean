import .fol tactic.tidy

open set function nat
universe variable u
namespace fol

local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`:0) := l


namespace Language
protected def sum (L L' : Language) : Language :=
⟨λn, L.functions n ⊕ L'.functions n, λ n, L.relations n ⊕ L'.relations n⟩

def symbols (L : Language) := (Σl, L.functions l) ⊕ (Σl, L.relations l)
end Language

-- section
-- variable {L : Language}


-- def symbols_in_term : ∀{l}, preterm L l → set L.symbols
-- | _ &k          := ∅
-- | l (func f)    := {sum.inl ⟨l,f⟩}
-- | _ (app t₁ t₂) := symbols_in_term t₁ ∪ symbols_in_term t₂

-- def symbols_in_formula : ∀{l}, preformula L l → set L.symbols
-- | _ falsum       := ∅
-- | _ (t₁ ≃ t₂)    := symbols_in_term t₁ ∪ symbols_in_term t₂
-- | l (rel R)      := {sum.inr ⟨l, R⟩}
-- | _ (apprel f t) := symbols_in_formula f ∪ symbols_in_term t
-- | _ (f₁ ⟹ f₂)   := symbols_in_formula f₁ ∪ symbols_in_formula f₂
-- | _ (∀' f)       := symbols_in_formula f

-- def symbols_in_prf : ∀{Γ : set $ formula L} {f : formula L} (P : Γ ⊢ f), set L.symbols
-- | Γ f (axm h)              := symbols_in_formula f
-- | Γ (f₁ ⟹ f₂) (impI P)    := symbols_in_prf P ∪ symbols_in_formula f₁
-- | Γ f₂ (impE f₁ P₁ P₂)     := symbols_in_prf P₁ ∪ symbols_in_prf P₂
-- | Γ f (falsumE P)          := symbols_in_prf P ∪ symbols_in_formula f
-- | Γ (∀' f) (allI P)        := symbols_in_prf P
-- | Γ _ (allE₂ f t P)        := symbols_in_prf P ∪ symbols_in_term t
-- | Γ (_ ≃ t) (ref _ _)     := symbols_in_term t
-- | Γ _ (subst₂ s t f P₁ P₂) := symbols_in_prf P₁ ∪ symbols_in_prf P₂

-- def interpolation : ∀{Γ : set $ formula L} {f : formula L} (P : Γ ⊢ f), 
--   Σ' (f' : formula L) (P₁ : Γ ⊢ f') (P₂ : {f'} ⊢ f), 
--     symbols_in_prf P₁ ⊆ ⋃₀ (symbols_in_formula '' Γ) ∧ 
--     symbols_in_prf P₂ ⊆ symbols_in_formula f ∧ 
--     symbols_in_formula f' ⊆ ⋃₀ (symbols_in_formula '' Γ) ∩ symbols_in_formula f := 
-- sorry -- probably the last property follows automatically
  


-- end

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

lemma Lhom_funext {L1} {L2} {F G : L1 →ᴸ L2} (h_fun : F.on_function = G.on_function ) (h_rel : F.on_relation = G.on_relation ) : F = G :=
by {cases F with Ff Fr, cases G with Gf Gr, simp only *, exact and.intro h_fun h_rel}

local infix ` ∘ `:60 := Lhom.comp

@[simp]lemma id_is_left_identity {L1 L2} {F : L1 →ᴸ L2} : (Lhom.id L2) ∘ F = F := by {cases F, refl}

@[simp]lemma id_is_right_identity {L1 L2} {F : L1 →ᴸ L2} : F ∘ (Lhom.id L1) = F := by {cases F, refl}

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
| _ &k          n m := by simp
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

@[simp] def on_formula_apps_rel : ∀{l} (f : preformula L l) (ts : dvector (term L) l),
  ϕ.on_formula (apps_rel f ts) = apps_rel (ϕ.on_formula f) (ts.map ϕ.on_term)
| _ f []       := by refl
| _ f (t'::ts) := by simp*

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


/- Various lemmas of the shape "on_etc is a functor to Type*" -/
@[simp]lemma comp_on_function {L1} {L2} {L3} (g : L2 →ᴸ L3) (f : L1 →ᴸ L2):
      (g ∘ f).on_function =
      begin intro n, let g1 := g.on_function, let f1 := f.on_function,
      exact function.comp (@g1 n) (@f1 n) end
      := by refl

/- comp_on_function with explicit nat parameter -/
@[simp]lemma comp_on_function' {L1} {L2} {L3} (g : L2 →ᴸ L3) (f : L1 →ᴸ L2) (n):
      @on_function L1 L3 (g ∘ f) n  =
      function.comp (@on_function L2 L3 g n) (@on_function L1 L2 f n)
      := by refl

@[simp]lemma comp_on_relation {L1} {L2} {L3} (g : L2 →ᴸ L3) (f : L1 →ᴸ L2) :
      (g ∘ f).on_relation =
      begin intro n, let g1 := g.on_relation, let f1 := f.on_relation,
      exact function.comp (@g1 n) (@f1 n) end
      := by refl

/- comp_on_relation with explicit nat parameter -/
@[simp]lemma comp_on_relation' {L1} {L2} {L3} (g : L2 →ᴸ L3) (f : L1 →ᴸ L2) (n):
      @on_relation L1 L3 (g ∘ f) n  =
      function.comp (@on_relation L2 L3 g n) (@on_relation L1 L2 f n)
      := by refl

/- The next two tidy proofs are unperformant, so maybe refactor later -/
/- Can't tag this as simp lemma for some reason -/
@[tidy]lemma comp_on_term {L1} {L2} {L3} {n l : ℕ}(g : L2 →ᴸ L3) (f : L1 →ᴸ L2) :
@on_term L1 L3 (g ∘ f) l = function.comp (@on_term L2 L3 g l) (@on_term L1 L2 f l) :=
by {fapply funext, intro x, induction x, tidy}

@[tidy]lemma comp_on_formula {L1} {L2} {L3} {n l : ℕ}(g : L2 →ᴸ L3) (f : L1 →ᴸ L2) :
@on_formula L1 L3 (g ∘ f) l = function.comp (@on_formula L2 L3 g l) (@on_formula L1 L2 f l) :=
by {fapply funext, intro x, induction x, tidy, all_goals{rw[comp_on_term], exact l}}

@[simp]lemma comp_on_bounded_term {L1} {L2} {L3} {n l : ℕ}(g : L2 →ᴸ L3) (f : L1 →ᴸ L2) :
@on_bounded_term L1 L3 (g ∘ f) n l = function.comp (@on_bounded_term L2 L3 g n l) (@on_bounded_term L1 L2 f n l) :=
by {fapply funext, intro x, tidy, induction x, tidy, all_goals{rw[comp_on_term], exact l}}

@[simp]lemma comp_on_bounded_formula {L1} {L2} {L3} {n l : ℕ}(g : L2 →ᴸ L3) (f : L1 →ᴸ L2) :
@on_bounded_formula L1 L3 (g ∘ f) n l = function.comp (@on_bounded_formula L2 L3 g n l) (@on_bounded_formula L1 L2 f n l) :=
by {fapply funext, intro x, tidy, induction x, tidy, all_goals{rw[comp_on_term], exact l}}

lemma id_term {L} : Πl, Π f, (@on_term L L (Lhom.id L) l) f = f
| _ &k          := by refl
| _ (func f)    := by refl
| l (app t₁ t₂) := by simp[id_term (l+1) t₁, id_term 0 t₂]

lemma id_formula {L} : Π l, Π f, (@on_formula L L (Lhom.id L) l) f = f
| _   falsum        := by refl
| _ (t₁ ≃ t₂)         := by simp[id_term]
| _ (rel R)       := by refl
| l (apprel f t)  := by {dsimp, rw[id_formula _ f, id_term _ t]}
| _ (f₁ ⟹ f₂)    := by {dsimp, rw[id_formula _ f₁, id_formula _ f₂]}
| _ (∀' f)        := by {dsimp, rw[id_formula _ f]}

lemma id_bounded_term {L} (n) : Πl, Π f, (@on_bounded_term L L (Lhom.id L) n l) f = f
| _ (bd_var k) := by refl
| _ (bd_func k) := by refl
| l (bd_app t₁ t₂) := by simp[id_bounded_term (l+1) t₁, id_bounded_term 0 t₂]

lemma id_bounded_formula {L} : Π n l, Π f, (@on_bounded_formula L L (Lhom.id L) n l) f = f
| _ _   bd_falsum        := by refl
| _ _ (t₁ ≃ t₂)         := by simp[id_bounded_term]
| _ _ (bd_rel R)       := by refl
| _ l (bd_apprel f t)  := by {dsimp, rw[id_bounded_formula _ _ f, id_bounded_term _ _ t]}
| _ _ (f₁ ⟹ f₂)    := by {dsimp, rw[id_bounded_formula _ _ f₁, id_bounded_formula _ _ f₂]}
| _ _ (∀' f)        := by {dsimp, rw[id_bounded_formula _ _ f]}

@[simp] def on_closed_term (t : closed_term L) : closed_term L' := ϕ.on_bounded_term t
@[simp] def on_sentence (f : sentence L) : sentence L' := ϕ.on_bounded_formula f

def on_prf {Γ : set $ formula L} {f : formula L} (h : Γ ⊢ f) : ϕ.on_formula '' Γ ⊢ ϕ.on_formula f :=
begin
  induction h,
  { apply axm, exact mem_image_of_mem _ h_h, },
  { apply impI, rw [←image_insert_eq], exact h_ih },
  { exact impE _ h_ih_h₁ h_ih_h₂, },
  { apply falsumE, rw [image_insert_eq] at h_ih, exact h_ih },
  { apply allI, rw [image_image] at h_ih ⊢, simp [image_congr' (on_formula_lift ϕ 1)] at h_ih, 
    exact h_ih },
  { apply allE _ _ h_ih, symmetry, apply on_formula_subst },
  { apply prf.ref },
  { simp at h_ih_h₂, apply subst _ h_ih_h₁ h_ih_h₂, simp }
end

def on_sprf {Γ : set $ sentence L} {f : sentence L} (h : Γ ⊢ f) : 
  ϕ.on_sentence '' Γ ⊢ ϕ.on_sentence f :=
by have := ϕ.on_prf h; simp only [sprf, Theory.fst, image_image, function.comp,
  on_bounded_formula_fst, on_sentence] at this ⊢; exact this
  

/- replace all symbols not in the image of ϕ by a new variable -/
noncomputable def reflect_term [has_decidable_range ϕ] (t : term L') (m : ℕ) : term L :=
term.elim (λk, &k ↑' 1 # m) 
     (λl f' ts' ts, if hf' : f' ∈ range (@on_function _ _ ϕ l)
       then apps (func (classical.some hf')) ts else &m) t

variable {ϕ}
lemma reflect_term_apps_pos [has_decidable_range ϕ] {l} {f : L'.functions l}
  (hf : f ∈ range (@on_function _ _ ϕ l)) (ts : dvector (term L') l) (m : ℕ) : 
  ϕ.reflect_term (apps (func f) ts) m = 
  apps (func (classical.some hf)) (ts.map (λt, ϕ.reflect_term t m)) :=
begin
  refine (term.elim_apps _ _ f ts).trans _, rw [dif_pos hf], refl
end

lemma reflect_term_apps_neg [has_decidable_range ϕ] {l} (f : L'.functions l) 
  (hf : f ∉ range (@on_function _ _ ϕ l)) (ts : dvector (term L') l) (m : ℕ) : 
  ϕ.reflect_term (apps (func f) ts) m = &m :=
begin
  refine (term.elim_apps _ _ f ts).trans _, rw [dif_neg hf]
end

@[simp] lemma reflect_term_var [has_decidable_range ϕ] (k : ℕ) (m : ℕ) : 
  ϕ.reflect_term &k m = &k ↑' 1 # m := by refl

@[simp] lemma reflect_term_on_term [has_decidable_range ϕ] (hϕ : is_injective ϕ) (t : term L) 
  (m : ℕ) : ϕ.reflect_term (ϕ.on_term t) m = t ↑' 1 # m :=
begin
  refine term.rec _ _ t; clear t; intros,
  { refl },
  { simp [reflect_term_apps_pos (mem_range_self f)], 
    rw [classical.some_eq f (λy hy, hϕ.on_function hy), dvector.map_congr_pmem ih_ts] }
end

lemma reflect_term_lift_at [has_decidable_range ϕ] (hϕ : is_injective ϕ) {n m m' : ℕ} (h : m ≤ m')
  (t : term L') : ϕ.reflect_term (t ↑' n # m) (m'+n) = ϕ.reflect_term t m' ↑' n # m :=
begin
  refine term.rec _ _ t; clear t; intros,
  { simp [-lift_term_at], rw[lift_term_at2_small _ _ _ h], simp },
  { by_cases h' : f ∈ range (@on_function _ _ ϕ l); simp [reflect_term_apps_pos, 
      reflect_term_apps_neg, h', h, dvector.map_congr_pmem ih_ts, -add_comm] }
end

lemma reflect_term_lift [has_decidable_range ϕ] (hϕ : is_injective ϕ) {n m : ℕ}
  (t : term L') : ϕ.reflect_term (t ↑ n) (m+n) = ϕ.reflect_term t m ↑ n :=
reflect_term_lift_at hϕ m.zero_le t

lemma reflect_term_subst [has_decidable_range ϕ] (hϕ : is_injective ϕ) (n m : ℕ) 
  (s t : term L') : 
  ϕ.reflect_term (t[s // n]) (m+n) = (ϕ.reflect_term t (m+n+1))[ϕ.reflect_term s m // n] :=
begin
  refine term.rec _ _ t; clear t; intros,
  { simp [-lift_term_at, -add_comm, -add_assoc], 
    apply lt_by_cases k n; intro h,
    { have h₂ : ¬(m + n ≤ k), from λh', not_le_of_gt h (le_trans (le_add_left n m) h'),
      have h₃ : ¬(m + n + 1 ≤ k), from λh', h₂ $ le_trans (le_succ _) h',
      simp [h, h₂, h₃, -add_comm, -add_assoc] },
    { have h₂ : ¬(m + n + 1 ≤ n), from not_le_of_gt (lt_of_le_of_lt (le_add_left n m) (lt.base _)) ,
      simp [h, h₂, reflect_term_lift hϕ, -add_comm, -add_assoc] },
    { have hk := one_le_of_lt h, 
      have h₄ : n < k + 1, from lt.trans h (lt.base k),
      by_cases h₂' : m + n + 1 ≤ k,
      { have h₂ : m + n + 1 ≤ k, from h₂',
        have h₃ : m + n ≤ k - 1, from (nat.le_sub_right_iff_add_le hk).mpr h₂,
        simp [h, h₂, h₃, h₄, -add_comm, -add_assoc], 
        rw [sub_add_eq_max, max_eq_left hk] },
      { have h₂ : ¬(m + n + 1 ≤ k), from h₂',
        have h₃ : ¬(m + n ≤ k - 1), from λh', h₂ $ (nat.le_sub_right_iff_add_le hk).mp h',
        simp [h, h₂, h₃, -add_comm, -add_assoc] }}},
  { have h : n < m + n + 1, from nat.lt_succ_of_le (nat.le_add_left n m),
    by_cases h' : f ∈ range (@on_function _ _ ϕ l); simp [reflect_term_apps_pos, 
      reflect_term_apps_neg, h, h', dvector.map_congr_pmem ih_ts, -add_comm, -add_assoc] }
end

variable (ϕ)

noncomputable def reflect_formula [has_decidable_range ϕ] (f : formula L') : 
  ∀(m : ℕ), formula L :=
formula.rec (λm, ⊥) (λt₁ t₂ m, ϕ.reflect_term t₁ m ≃ ϕ.reflect_term t₂ m)
  (λl R' xs' m, if hR' : R' ∈ range (@on_relation _ _ ϕ l)
       then apps_rel (rel (classical.some hR')) (xs'.map $ λt, ϕ.reflect_term t m) else ⊥)
   (λf₁' f₂' f₁ f₂ m, f₁ m ⟹ f₂ m) (λf' f m, ∀' f (m+1)) f

variable {ϕ}
lemma reflect_formula_apps_rel_pos [has_decidable_range ϕ] {l} {R : L'.relations l}
  (hR : R ∈ range (@on_relation _ _ ϕ l)) (ts : dvector (term L') l) (m : ℕ) : 
  ϕ.reflect_formula (apps_rel (rel R) ts) m = 
  apps_rel (rel (classical.some hR)) (ts.map (λt, ϕ.reflect_term t m)) :=
by simp [reflect_formula, formula.rec_apps_rel, dif_pos hR]

lemma reflect_formula_apps_rel_neg [has_decidable_range ϕ] {l} {R : L'.relations l} 
  (hR : R ∉ range (@on_relation _ _ ϕ l)) (ts : dvector (term L') l) (m : ℕ) : 
  ϕ.reflect_formula (apps_rel (rel R) ts) m = ⊥ :=
by simp [reflect_formula, formula.rec_apps_rel, dif_neg hR]

@[simp] lemma reflect_formula_equal [has_decidable_range ϕ] (t₁ t₂ : term L') (m : ℕ) : 
  ϕ.reflect_formula (t₁ ≃ t₂) m = ϕ.reflect_term t₁ m ≃ ϕ.reflect_term t₂ m := by refl
@[simp] lemma reflect_formula_imp [has_decidable_range ϕ] (f₁ f₂ : formula L') (m : ℕ) : 
  ϕ.reflect_formula (f₁ ⟹ f₂) m = ϕ.reflect_formula f₁ m ⟹ ϕ.reflect_formula f₂ m := by refl
@[simp] lemma reflect_formula_all [has_decidable_range ϕ] (f : formula L') (m : ℕ) : 
  ϕ.reflect_formula (∀' f) m = ∀' (ϕ.reflect_formula f (m+1)) := by refl

@[simp] lemma reflect_formula_on_formula [has_decidable_range ϕ] (hϕ : is_injective ϕ) 
  (f : formula L) : ∀(m : ℕ), ϕ.reflect_formula (ϕ.on_formula f) m = f ↑' 1 # m :=
begin
  refine formula.rec _ _ _ _ _ f; clear f; intros,
  { refl },
  { simp [hϕ] },
  { simp [reflect_formula_apps_rel_pos (mem_range_self R), hϕ], 
    rw [classical.some_eq R (λy hy, hϕ.on_relation hy)] },
  { simp* },
  { simp* }
end

lemma reflect_formula_lift_at [has_decidable_range ϕ] (hϕ : is_injective ϕ) {n m m' : ℕ} 
  (h : m ≤ m') (f : formula L') : 
  ϕ.reflect_formula (f ↑' n # m) (m'+n) = ϕ.reflect_formula f m' ↑' n # m :=
begin
  revert m m', refine formula.rec _ _ _ _ _ f; clear f; intros,
  { refl },
  { simp [reflect_term_lift_at hϕ h, -add_comm] },
  { by_cases h' : R ∈ range (@on_relation _ _ ϕ l); simp [reflect_formula_apps_rel_pos, 
      reflect_formula_apps_rel_neg, h', h, ts.map_congr (reflect_term_lift_at hϕ h), -add_comm] },
  { simp [ih₁ h, ih₂ h, -add_comm] },
  { simp [-add_comm, -add_assoc], rw [←ih], simp, exact add_le_add_right h 1 },
end

lemma reflect_formula_lift [has_decidable_range ϕ] (hϕ : is_injective ϕ) (n m : ℕ)
  (f : formula L') : ϕ.reflect_formula (f ↑ n) (m+n) = ϕ.reflect_formula f m ↑ n :=
reflect_formula_lift_at hϕ m.zero_le f

lemma reflect_formula_lift1 [has_decidable_range ϕ] (hϕ : is_injective ϕ) (m : ℕ)
  (f : formula L') : ϕ.reflect_formula (f ↑ 1) (m+1) = ϕ.reflect_formula f m ↑ 1 :=
reflect_formula_lift hϕ 1 m f

lemma reflect_formula_subst [has_decidable_range ϕ] (hϕ : is_injective ϕ) (f : formula L') 
  (n m : ℕ) (s : term L') : 
  ϕ.reflect_formula (f[s // n]) (m+n) = (ϕ.reflect_formula f (m+n+1))[ϕ.reflect_term s m // n] :=
begin
  revert n, refine formula.rec _ _ _ _ _ f; clear f; intros,
  { refl },
  { simp [reflect_term_subst hϕ, -add_comm] },
  { by_cases h' : R ∈ range (@on_relation _ _ ϕ l); simp [reflect_formula_apps_rel_pos, 
      reflect_formula_apps_rel_neg, h', ts.map_congr (reflect_term_subst hϕ n m s), -add_comm] },
  { simp [ih₁, ih₂, -add_comm] },
  { simp [-add_comm, ih] },
end

@[simp] lemma reflect_formula_subst0 [has_decidable_range ϕ] (hϕ : is_injective ϕ) (m : ℕ)
  (f : formula L') (s : term L') : 
  ϕ.reflect_formula (f[s // 0]) m = (ϕ.reflect_formula f (m+1))[ϕ.reflect_term s m // 0] :=
reflect_formula_subst hϕ f 0 m s

noncomputable def reflect_prf_gen [has_decidable_range ϕ] (hϕ : is_injective ϕ) {Γ} 
  {f : formula L'} (m) (H : Γ ⊢ f) : (λf, ϕ.reflect_formula f m) '' Γ ⊢ ϕ.reflect_formula f m :=
begin
  induction H generalizing m,
  { apply axm, apply mem_image_of_mem _ H_h },
  { apply impI, have h := @H_ih m, rw [image_insert_eq] at h, exact h },
  { apply impE, apply H_ih_h₁, apply H_ih_h₂ },
  { apply falsumE, have h := @H_ih m, rw [image_insert_eq] at h, exact h },
  { apply allI, rw [image_image], have h := @H_ih (m+1), rw [image_image] at h, 
    apply cast _ h, congr1, apply image_congr' (reflect_formula_lift1 hϕ m) },
  { apply allE, have h := @H_ih m, simp at h, exact h, symmetry,
    apply reflect_formula_subst0 hϕ },
  { apply ref },
  { apply subst, have h := @H_ih_h₁ m, simp at h, exact h,
    have h := @H_ih_h₂ m, simp [hϕ] at h, exact h, simp [hϕ] },
end

noncomputable def reflect_prf {Γ : set $ formula L} {f : formula L} (hϕ : ϕ.is_injective)
  (h : ϕ.on_formula '' Γ ⊢ ϕ.on_formula f) : Γ ⊢ f :=
begin
  haveI : has_decidable_range ϕ :=
    ⟨λl f, classical.prop_decidable _, λl R, classical.prop_decidable _⟩,
  apply reflect_prf_lift1,
  have := reflect_prf_gen hϕ 0 h, simp [image_image, hϕ] at this, exact this
end

noncomputable def reflect_sprf {Γ : set $ sentence L} {f : sentence L} (hϕ : ϕ.is_injective) 
  (h : ϕ.on_sentence '' Γ ⊢ ϕ.on_sentence f) : Γ ⊢ f :=
by { apply reflect_prf hϕ, simp only [sprf, Theory.fst, image_image, function.comp,
     on_bounded_formula_fst, on_sentence] at h ⊢, exact h }

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

lemma on_bounded_term_inj (h : ϕ.is_injective) {n} {l} : injective (ϕ.on_bounded_term : bounded_preterm L n l → bounded_preterm L' n l) :=
begin
  intros x y hxy, induction x generalizing y; cases y; try {injection hxy with hxy' hxy''},
  { rw [hxy'] },
  { rw [h.on_function hxy'] },
  { congr1, exact x_ih_t hxy', exact x_ih_s hxy'' }
end

lemma on_bounded_formula_inj (h : ϕ.is_injective) {n l}:
  injective (ϕ.on_bounded_formula : bounded_preformula L n l → bounded_preformula L' n l) :=
begin
  intros x y hxy, induction x generalizing y; cases y; try {injection hxy with hxy' hxy''},
  { refl },
  { rw [on_bounded_term_inj h hxy', on_bounded_term_inj h hxy''] },
  { rw [h.on_relation hxy'] },
  { rw [x_ih hxy', on_bounded_term_inj h hxy''] },
  { rw [x_ih_f₁ hxy', x_ih_f₂ hxy''] },
  { rw [x_ih hxy'] }
end

variable (ϕ)

/-- Given L → L' and an L'-structure S, the reduct of S to L is the L-structure given by
restricting interpretations from L' to L --/
def reduct (S : Structure L') : Structure L :=
⟨ S.carrier, λn f, S.fun_map $ ϕ.on_function f, λn R, S.rel_map $ ϕ.on_relation R⟩ 

variable {ϕ}

@[simp] def reduct_coe (S : Structure L') : ↥(reduct ϕ S) = S := 
by refl

def reduct_id {S : Structure L'} : S → reduct ϕ S := id

@[simp] lemma reduct_term_eq {S : Structure L'} (hϕ : ϕ.is_injective) {n} : 
  Π(xs : dvector S n) {l} (t : bounded_preterm L n l) (xs' : dvector S l), realize_bounded_term xs (on_bounded_term ϕ t) xs' = @realize_bounded_term L (reduct ϕ S) n xs l t xs'
| xs _ (bd_var k)   xs' := by refl
| xs _ (bd_func f)  xs' := by refl
| xs l (bd_app t s) xs' := by simp*

lemma reduct_bounded_formula_iff {S : Structure L'} (hϕ : ϕ.is_injective) : Π{n l} (xs : dvector S n) (xs' : dvector S l) (f : bounded_preformula L n l), 
  realize_bounded_formula xs (on_bounded_formula ϕ f) xs' ↔ @realize_bounded_formula L (reduct ϕ S) n l xs f xs'
| _ _ xs xs' (bd_falsum)      := by refl
| _ _ xs xs' (bd_equal t₁ t₂) := by simp [hϕ]
| _ _ xs xs' (bd_rel R)       := by refl
| _ _ xs xs' (bd_apprel f t)  := by simp*
| _ _ xs xs' (f₁ ⟹ f₂)       := by simp*
| _ _ xs xs' (∀' f)           := by apply forall_congr; intro x;simp*

lemma reduct_ssatisfied {S : Structure L'} {f : sentence L} (hϕ : ϕ.is_injective) 
  (h : S ⊨ ϕ.on_sentence f) : ϕ.reduct S ⊨ f :=
(reduct_bounded_formula_iff hϕ ([]) ([]) f).mp h

def reduct_all_ssatisfied {S : Structure L'} {T : Theory L} (hϕ : ϕ.is_injective) 
  (h : S ⊨ ϕ.on_sentence '' T) : ϕ.reduct S ⊨ T :=
λf hf, reduct_ssatisfied hϕ $ h $ mem_image_of_mem _ hf

lemma reduct_nonempty_of_nonempty {S : Structure L'} (H : nonempty S) : nonempty (reduct ϕ S) :=
by {apply nonempty.map, repeat{assumption}, exact reduct_id}

variable (ϕ)
def Theory_induced (T : Theory L) : Theory L' := ϕ.on_sentence '' T

variable {ϕ}
lemma is_consistent_Theory_induced (hϕ : ϕ.is_injective) {T : Theory L} (hT : is_consistent T) : 
  is_consistent (ϕ.Theory_induced T) :=
λH, hT $ H.map $ λh, reflect_sprf hϕ (by apply h)

end Lhom


end fol




-- instance nonempty_Language_over : nonempty (Language_over) :=
--   begin fapply nonempty.intro, exact ⟨L, language_id_morphism L⟩ end

--TODO define map induced by a language_morphism on terms/preterms, formulas/preformulas, sets of formulas/theories
