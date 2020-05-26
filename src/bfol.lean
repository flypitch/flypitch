/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
/- A development of boolean-valued first-order logic in Lean.
-/

import .fol order.complete_boolean_algebra

open nat set fol
universe variables u v w

local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`:0) := l
local infix ⇒ := _root_.imp
local infix ` ⟷ `:40 := _root_.biimp

namespace fol

section bfol

/- bModel β Theory -/

/- an L-Structure is a type S with interpretations of the functions and relations on S -/
variables (L : Language.{u}) (β : Type v) [complete_boolean_algebra β]

structure bStructure :=
(carrier : Type u)
(fun_map : ∀{n}, L.functions n → dvector carrier n → carrier)
(rel_map : ∀{n}, L.relations n → dvector carrier n → β)
(eq : carrier → carrier → β)
(eq_refl : ∀ x, eq x x = ⊤)
(eq_symm : ∀ x y, eq x y = eq y x)
(eq_trans : ∀{x} y {z}, eq x y ⊓ eq y z ≤ eq x z)
(fun_congr : ∀{n} (f : L.functions n) (x y : dvector carrier n),
  (x.map2 eq y).fInf ≤ eq (fun_map f x) (fun_map f y))
(rel_congr : ∀{n} (R : L.relations n) (x y : dvector carrier n),
  (x.map2 eq y).fInf ⊓ rel_map R x ≤ rel_map R y)

variables {L β}
instance has_coe_bStructure : has_coe_to_sort (bStructure L β) :=
⟨Type u, bStructure.carrier⟩
attribute [simp] bStructure.eq_refl

variables {S : bStructure L β} {v v' : ℕ → S} {n l : ℕ}
@[simp] lemma eq_drefl : ∀{n} (x : dvector S n), (x.map2 S.eq x).fInf = ⊤
| _ ([])    := rfl
| _ (x::xs) := by simp [eq_drefl]

lemma eq_dsymm : ∀{n} (x y : dvector S n), (x.map2 S.eq y).fInf = (y.map2 S.eq x).fInf
| _ ([])    ([])    := rfl
| _ (x::xs) (y::ys) := by simp [S.eq_symm x y, eq_dsymm]

lemma eq_dtrans : ∀{n} {x : dvector S n} (y : dvector S n) {z : dvector S n},
  (x.map2 S.eq y).fInf ⊓ (y.map2 S.eq z).fInf ≤ (x.map2 S.eq z).fInf
| _ ([])    ([])    ([])    := by simp
| _ (x::xs) (y::ys) (z::zs) :=
  begin
    simp, split,
    exact le_trans (inf_le_inf inf_le_left inf_le_left) (S.eq_trans y),
    exact le_trans (inf_le_inf inf_le_right inf_le_right) (eq_dtrans ys)
  end

@[simp] def subst_realize_congr1 (v v' : ℕ → S) (x : S) (n : ℕ) :
  (⨅ (n : ℕ), S.eq (v n) (v' n)) ≤ ⨅(k : ℕ), S.eq (v[x // n] k) (v'[x // n] k) :=
by { rw [le_infi_iff], intro k, apply decidable.lt_by_cases k n; intro h; simp [h]; apply infi_le }

@[simp] def subst_realize_congr2 (v : ℕ → S) (x y : S) :
  S.eq x y ≤ ⨅(k : ℕ), S.eq (v[x // n] k) (v[y // n] k) :=
by { rw [le_infi_iff], intro k, apply decidable.lt_by_cases k n; intro h; simp [h] }


/- realization of terms -/
@[simp] def boolean_realize_term (v : ℕ → S) :
  ∀{l} (t : preterm L l) (xs : dvector S l), S.carrier
| _ &k          xs := v k
| _ (func f)    xs := S.fun_map f xs
| _ (app t₁ t₂) xs := boolean_realize_term t₁ $ boolean_realize_term t₂ ([])::xs

lemma boolean_realize_term_congr' {v v' : ℕ → S} (h : ∀n, v n = v' n) :
  ∀{l} (t : preterm L l) (xs : dvector S l), boolean_realize_term v t xs = boolean_realize_term v' t xs
| _ &k          xs := h k
| _ (func f)    xs := by refl
| _ (app t₁ t₂) xs := by dsimp; rw [boolean_realize_term_congr' t₁, boolean_realize_term_congr' t₂]

lemma boolean_realize_term_subst (v : ℕ → S) : ∀{l} (n : ℕ) (t : preterm L l)
  (s : term L) (xs : dvector S l), boolean_realize_term (v[boolean_realize_term v (s ↑ n) ([]) // n]) t xs = boolean_realize_term v (t[s // n]) xs
| _ n &k          s [] :=
  by apply decidable.lt_by_cases k n; intro h;[simp [h], {subst h; simp}, simp [h]]
| _ n (func f)    s xs := by refl
| _ n (app t₁ t₂) s xs := by dsimp; simp*

lemma boolean_realize_term_subst_lift (v : ℕ → S) (x : S) (m : ℕ) : ∀{l} (t : preterm L l)
  (xs : dvector S l), boolean_realize_term (v [x // m]) (t ↑' 1 # m) xs = boolean_realize_term v t xs
| _ &k          [] :=
  begin
    by_cases h : m ≤ k,
    { have : m < k + 1, from lt_succ_of_le h, simp* },
    { have : k < m, from lt_of_not_ge h, simp* }
  end
| _ (func f)    xs := by refl
| _ (app t₁ t₂) xs := by simp*

lemma boolean_realize_term_congr_gen (v v' : ℕ → S) :
  ∀{l} (t : preterm L l) (xs xs' : dvector S l),
  (⨅(n : ℕ), S.eq (v n) (v' n)) ⊓ (xs.map2 S.eq xs').fInf ≤
    S.eq (boolean_realize_term v t xs) (boolean_realize_term v' t xs')
| _ &k          xs xs' := le_trans inf_le_left (infi_le _ k)
| _ (func f)    xs xs' := by { dsimp, apply le_trans inf_le_right, apply S.fun_congr }
| _ (app t₁ t₂) xs xs' :=
  begin
    refine le_trans _ (boolean_realize_term_congr_gen t₁ _ _),
    simp only [dvector.map2, dvector.fInf_cons],
    rw [le_inf_iff], split, apply inf_le_left,
    apply inf_le_inf,
    { refine le_trans _ (boolean_realize_term_congr_gen t₂ _ _), simp [-le_infi_iff] },
    reflexivity
  end

lemma boolean_realize_term_congr (v v' : ℕ → S) {l} (t : preterm L l) (xs : dvector S l) :
  (⨅(n : ℕ), S.eq (v n) (v' n)) ≤
    S.eq (boolean_realize_term v t xs) (boolean_realize_term v' t xs) :=
begin
  refine le_trans _ (boolean_realize_term_congr_gen v v' t _ _),
  simp only [le_inf_iff, dvector.map2, le_refl, and_true, eq_drefl, le_top],
end

lemma boolean_realize_term_subst_congr (v : ℕ → S) {n} (s s' : term L) :
  ∀{l} (t : preterm L l) (xs : dvector S l),
  S.eq (boolean_realize_term v (s ↑ n) ([])) (boolean_realize_term v (s' ↑ n) ([])) ≤
  S.eq (boolean_realize_term v (t[s//n]) xs) (boolean_realize_term v (t[s'//n]) xs) :=
begin
intros,
  rw [← boolean_realize_term_subst, ← boolean_realize_term_subst],
  refine le_trans _ (boolean_realize_term_congr _ _ _ _),
  apply subst_realize_congr2
end

/- realization of formulas -/
@[simp] def boolean_realize_formula : ∀{l}, (ℕ → S) → preformula L l → dvector S l → β
| _ v falsum       xs := ⊥
| _ v (t₁ ≃ t₂)    xs := S.eq (boolean_realize_term v t₁ xs) (boolean_realize_term v t₂ xs)
| _ v (rel R)      xs := S.rel_map R xs
| _ v (apprel f t) xs := boolean_realize_formula v f $ boolean_realize_term v t ([])::xs
| _ v (f₁ ⟹ f₂)   xs := boolean_realize_formula v f₁ xs ⇒ boolean_realize_formula v f₂ xs
| _ v (∀' f)       xs := ⨅(x : S), boolean_realize_formula (v [x // 0]) f xs

lemma boolean_realize_formula_congr' : ∀{l} {v v' : ℕ → S} (h : ∀n, v n = v' n)
  (f : preformula L l) (xs : dvector S l), boolean_realize_formula v f xs = boolean_realize_formula v' f xs
| _ v v' h falsum       xs := by refl
| _ v v' h (t₁ ≃ t₂)    xs := by simp [boolean_realize_term_congr' h]
| _ v v' h (rel R)      xs := by refl
| _ v v' h (apprel f t) xs := by simp [boolean_realize_term_congr' h]; rw [boolean_realize_formula_congr' h]
| _ v v' h (f₁ ⟹ f₂)   xs := by dsimp; rw [boolean_realize_formula_congr' h, boolean_realize_formula_congr' h]
| _ v v' h (∀' f)       xs :=
  by apply congr_arg infi; apply funext; intro x; apply boolean_realize_formula_congr'; intro n; apply subst_realize_congr h

lemma boolean_realize_formula_subst : ∀{l} (v : ℕ → S) (n : ℕ) (f : preformula L l)
  (s : term L) (xs : dvector S l), boolean_realize_formula (v[boolean_realize_term v (s ↑ n) ([]) // n]) f xs = boolean_realize_formula v (f[s // n]) xs
| _ v n falsum       s xs := by refl
| _ v n (t₁ ≃ t₂)    s xs := by simp [boolean_realize_term_subst]
| _ v n (rel R)      s xs := by refl
| _ v n (apprel f t) s xs := by simp [boolean_realize_term_subst]; rw boolean_realize_formula_subst
| _ v n (f₁ ⟹ f₂)   s xs := by dsimp; congr' 1; rw boolean_realize_formula_subst
| _ v n (∀' f)       s xs :=
  begin
    apply congr_arg infi; apply funext; intro x,
    rw [←boolean_realize_formula_subst], apply boolean_realize_formula_congr',
    intro k, rw [subst_realize2_0, ←boolean_realize_term_subst_lift v x 0, lift_term_def, lift_term2]
  end

lemma boolean_realize_formula_subst0 {l} (v : ℕ → S) (f : preformula L l) (s : term L) (xs : dvector S l) :
  boolean_realize_formula (v[boolean_realize_term v s ([]) // 0]) f xs = boolean_realize_formula v (f[s // 0]) xs :=
by have h := boolean_realize_formula_subst v 0 f s; simp at h; exact h xs

lemma boolean_realize_formula_subst_lift : ∀{l} (v : ℕ → S) (x : S) (m : ℕ)
  (f : preformula L l) (xs : dvector S l), boolean_realize_formula (v [x // m]) (f ↑' 1 # m) xs = boolean_realize_formula v f xs
| _ v x m falsum       xs := by refl
| _ v x m (t₁ ≃ t₂)    xs := by simp [boolean_realize_term_subst_lift]
| _ v x m (rel R)      xs := by refl
| _ v x m (apprel f t) xs :=
  by simp [boolean_realize_term_subst_lift]; rw boolean_realize_formula_subst_lift
| _ v x m (f₁ ⟹ f₂)   xs := by dsimp; congr' 1; apply boolean_realize_formula_subst_lift
| _ v x m (∀' f)       xs :=
  begin
    apply congr_arg infi; apply funext, intro x',
    rw [boolean_realize_formula_congr' (subst_realize2_0 _ _ _ _),
      boolean_realize_formula_subst_lift]
  end

lemma boolean_realize_formula_congr_gen : ∀(v v' : ℕ → S) {l} (f : preformula L l)
  (xs xs' : dvector S l),
  (⨅(n : ℕ), S.eq (v n) (v' n)) ⊓ (xs.map2 S.eq xs').fInf ⊓ boolean_realize_formula v f xs ≤
    boolean_realize_formula v' f xs'
| v v' _ falsum       xs xs' := inf_le_right
| v v' _ (t₁ ≃ t₂)    xs xs' :=
  begin
    refine le_trans _ (S.eq_trans (boolean_realize_term v t₂ xs)),
    rw le_inf_iff, split,
    { refine le_trans _ (S.eq_trans (boolean_realize_term v t₁ xs)),
      apply inf_le_inf,
      { rw [S.eq_symm], apply boolean_realize_term_congr_gen },
      refl },
    apply le_trans inf_le_left, apply boolean_realize_term_congr_gen
  end
| v v' _ (rel R)      xs xs' := le_trans (inf_le_inf inf_le_right (le_refl _)) (S.rel_congr R xs xs')
| v v' _ (apprel f t) xs xs' :=
  begin
    simp, refine le_trans _ (boolean_realize_formula_congr_gen v v' f
      (boolean_realize_term v t dvector.nil :: xs) _),
    rw [le_inf_iff], split,
    { apply le_trans inf_le_left, rw [le_inf_iff], split, apply inf_le_left,
      rw [dvector.map2, dvector.fInf_cons],
      apply inf_le_inf, apply boolean_realize_term_congr, reflexivity },
    { apply inf_le_right }
  end
| v v' _ (f₁ ⟹ f₂)   xs xs' :=
  begin
    dsimp, simp only [_root_.imp, inf_sup_left], apply sup_le_sup,
    { apply le_neg_of_inf_eq_bot,
      convert sub_eq_bot_of_le (boolean_realize_formula_congr_gen v' v f₁ xs' xs) using 1,
      rw [inf_comm, @inf_comm _ _ (-_), @inf_assoc _ _ (has_inf.inf _ _),
      @inf_assoc _ _ (has_inf.inf _ _)],
      congr' 1, congr' 1, congr' 1, apply funext, intro n, apply S.eq_symm,
      apply eq_dsymm, apply inf_comm },
    { apply boolean_realize_formula_congr_gen }
  end
| v v' _ (∀' f)       xs xs' :=
  begin
    dsimp only [boolean_realize_formula], rw le_infi_iff, intro x,
    refine le_trans _ (boolean_realize_formula_congr_gen (v[x//0]) _ _ xs _),
    apply inf_le_inf, apply inf_le_inf, apply subst_realize_congr1, refl, apply infi_le
  end

lemma boolean_realize_formula_congr (v v' : ℕ → S) {l} (f : preformula L l) (xs : dvector S l) :
  (⨅(n : ℕ), S.eq (v n) (v' n)) ⊓ boolean_realize_formula v f xs ≤
  boolean_realize_formula v' f xs :=
begin
  refine le_trans _ (boolean_realize_formula_congr_gen v v' f xs xs),
  simp [le_inf_iff, dvector.map2, le_refl, and_true, eq_drefl, le_top],
end

lemma boolean_realize_formula_subst_congr (v : ℕ → S) (s s' : term L) :
  ∀{n l} (f : preformula L l) (xs : dvector S l),
  S.eq (boolean_realize_term v (s ↑ n) ([])) (boolean_realize_term v (s' ↑ n) ([])) ⊓
  boolean_realize_formula v (f[s//n]) xs ≤ boolean_realize_formula v (f[s'//n]) xs :=
begin
intros,
  rw [← boolean_realize_formula_subst, ← boolean_realize_formula_subst],
  refine le_trans _
    (boolean_realize_formula_congr (v[boolean_realize_term v (s ↑ n) ([]) // n]) _ _ _),
  simp, intro k,
  apply decidable.lt_by_cases k n; intro h; simp [h]
end

lemma boolean_realize_formula_subst_congr0 (v : ℕ → S) (s s' : term L) {l} (f : preformula L l)
  (xs : dvector S l) :
  S.eq (boolean_realize_term v s ([])) (boolean_realize_term v s' ([])) ⊓
  boolean_realize_formula v (f[s//0]) xs ≤ boolean_realize_formula v (f[s'//0]) xs :=
begin
  convert boolean_realize_formula_subst_congr v s s' f xs; simp
end

@[simp] lemma boolean_realize_formula_not (v : ℕ → S) (f : formula L) :
   boolean_realize_formula v (∼f) ([]) = -boolean_realize_formula v f ([]) :=
by simp [not]

/- the following definitions of provability and satisfiability are not exactly how you normally define them, since we define it for formulae instead of sentences. If all the formulae happen to be sentences, then these definitions are equivalent to the normal definitions (the realization of closed terms and sentences are independent of the realizer v).
 -/
-- def all_prf (T T' : set (formula L)) := ∀{{f}}, f ∈ T' → T ⊢ f
-- infix ` ⊢ `:51 := fol.all_prf -- input: |- or \vdash

def boolean_realize_formula_glb (S : bStructure L β) (f : formula L) : β :=
⨅(v : ℕ → S), boolean_realize_formula v f ([])

notation `⟦`:max f `⟧[` S `]ᵤ`:0 := boolean_realize_formula_glb S f

-- def all_bsatisfied_in (S : bStructure L β) (T : set (formula L)) := ∀{{f}}, f ∈ T → S ⊨ᵇ f
-- infix ` ⊨ᵇ `:51 := fol.all_satisfied_in -- input using \|= or \vDash, but not using \bModels

variable (β)
def bstatisfied (T : set (formula L)) (f : formula L) : Prop :=
∀(S : bStructure L β) (v : ℕ → S),
  (⨅(f' ∈ T), boolean_realize_formula v (f' : formula L) ([])) ≤ boolean_realize_formula v f ([])
variable {β}

notation T ` ⊨ᵤ[`:51 β`] `:0 f := fol.bstatisfied β T f -- input using \|= or \vDash, but not using \bModels

-- def all_bstatisfied (T T' : set (formula L)) := ∀{{f}}, f ∈ T' → T ⊨ᵇ f
-- infix ` ⊨ᵇ `:51 := fol.all_bstatisfied -- input using \|= or \vDash, but not using \bModels

-- def bstatisfied_in_trans {T : set (formula L)} {f : formula L} (H' : S ⊨ᵇ T)
--   (H : T ⊨ᵇ f) : S ⊨ᵇ f :=
-- λv, H S v $ λf' hf', H' hf' v

-- def all_bstatisfied_in_trans  {T T' : set (formula L)} (H' : S ⊨ᵇ T) (H : T ⊨ᵇ T') :
--   S ⊨ᵇ T' :=
-- λf hf, bstatisfied_in_trans H' $ H hf

def bstatisfied_of_mem {T : set (formula L)} {f : formula L} (hf : f ∈ T) : T ⊨ᵤ[β] f :=
λS v, le_trans (infi_le _ f) (infi_le _ hf)

-- def all_bstatisfied_of_subset {T T' : set (formula L)} (h : T' ⊆ T) : T ⊨ᵇ T' :=
-- λf hf, bstatisfied_of_mem $ h hf

-- def bstatisfied_trans {T₁ T₂ : set (formula L)} {f : formula L} (H' : T₁ ⊨ᵇ T₂) (H : T₂ ⊨ᵇ f) : T₁ ⊨ᵇ f :=
-- λS v h, H S v $ λf' hf', H' hf' S v h

-- def all_bstatisfied_trans {T₁ T₂ T₃ : set (formula L)} (H' : T₁ ⊨ᵇ T₂) (H : T₂ ⊨ᵇ T₃) : T₁ ⊨ᵇ T₃ :=
-- λf hf, bstatisfied_trans H' $ H hf

def bstatisfied_weakening {T T' : set (formula L)} (H : T ⊆ T') {f : formula L} (HT : T ⊨ᵤ[β] f) :
  T' ⊨ᵤ[β] f :=
begin
  intros S v, refine le_trans _ (HT S v),
  apply infi_le_infi, intro f,
  apply infi_le_infi2, intro hf,
  refine ⟨H hf, _⟩, refl
end

/- soundness for a set of formulae with boolean models -/
lemma boolean_formula_soundness {Γ : set (formula L)} {A : formula L} (H : Γ ⊢ A) : Γ ⊨ᵤ[β] A :=
begin
  induction H; intros S v,
  { exact bstatisfied_of_mem H_h S v },
  { simp [deduction_simp], refine le_trans _ (H_ih S v), rw [inf_comm, infi_insert] },
  { refine le_trans _ (imp_inf_le _ _), swap,
    refine le_trans _ (inf_le_inf (H_ih_h₁ S v) (H_ih_h₂ S v)), rw [inf_idem] },
  { apply le_of_sub_eq_bot, apply bot_unique, refine le_trans _ (H_ih S v),
    rw [infi_insert, boolean_realize_formula_not] },
  { simp, intro x, refine le_trans _ (H_ih S _), apply le_infi, intro f,
    apply le_infi, rintro ⟨f, hf, rfl⟩, rw [boolean_realize_formula_subst_lift],
    exact le_trans (infi_le _ f) (infi_le _ hf) },
  { rw [←boolean_realize_formula_subst0], apply le_trans (H_ih S v), apply infi_le },
  { dsimp, rw [S.eq_refl], apply le_top },
  { refine le_trans _ (boolean_realize_formula_subst_congr0 v H_s H_t H_f ([])),
    exact le_inf (H_ih_h₁ S v) (H_ih_h₂ S v) }
end

@[simp] def boolean_realize_bounded_term {n} (v : dvector S n) :
  ∀{l} (t : bounded_preterm L n l) (xs : dvector S l), S.carrier
| _ &k             xs := v.nth k.1 k.2
| _ (bd_func f)    xs := S.fun_map f xs
| _ (bd_app t₁ t₂) xs := boolean_realize_bounded_term t₁ $ boolean_realize_bounded_term t₂ ([])::xs

@[reducible] def boolean_realize_closed_term (S : bStructure L β) (t : closed_term L) : S :=
boolean_realize_bounded_term ([]) t ([])

lemma boolean_realize_bounded_term_eq {n} {v₁ : dvector S n} {v₂ : ℕ → S}
  (hv : ∀k (hk : k < n), v₂ k = v₁.nth k hk) : ∀{l} (t : bounded_preterm L n l)
  (xs : dvector S l), boolean_realize_term v₂ t.fst xs = boolean_realize_bounded_term v₁ t xs
| _ &k             xs := hv k.1 k.2
| _ (bd_func f)    xs := by refl
| _ (bd_app t₁ t₂) xs := by dsimp; simp [boolean_realize_bounded_term_eq]

lemma boolean_realize_bounded_term_irrel' {n n'} {v₁ : dvector S n} {v₂ : dvector S n'}
  (h : ∀m (hn : m < n) (hn' : m < n'), v₁.nth m hn = v₂.nth m hn')
  {l} (t : bounded_preterm L n l) (t' : bounded_preterm L n' l)
  (ht : t.fst = t'.fst) (xs : dvector S l) :
  boolean_realize_bounded_term v₁ t xs = boolean_realize_bounded_term v₂ t' xs :=
begin
  induction t; cases t'; injection ht with ht₁ ht₂,
  { simp, cases t'_1; dsimp at ht₁, subst ht₁, exact h t.val t.2 t'_1_is_lt },
  { subst ht₁, refl },
  { simp [t_ih_t t'_t ht₁, t_ih_s t'_s ht₂] }
end

lemma boolean_realize_bounded_term_irrel {n} {v₁ : dvector S n}
  (t : bounded_term L n) (t' : closed_term L) (ht : t.fst = t'.fst) (xs : dvector S 0) :
  boolean_realize_bounded_term v₁ t xs = boolean_realize_closed_term S t' :=
by cases xs; exact boolean_realize_bounded_term_irrel'
  (by intros m hm hm'; exfalso; exact not_lt_zero m hm') t t' ht ([])

@[simp] lemma boolean_realize_bounded_term_cast_eq_irrel {n m l} {h : n = m} {v : dvector S m} {t : bounded_preterm L n l} (xs : dvector S l) :
boolean_realize_bounded_term v (t.cast_eq h) xs = boolean_realize_bounded_term (v.cast h.symm) t xs := by {subst h, induction t, refl, refl, simp*}

@[simp] lemma boolean_realize_bounded_term_dvector_cast_irrel {n m l} {h : n = m} {v : dvector S n} {t : bounded_preterm L n l} {xs : dvector S l} :
boolean_realize_bounded_term (v.cast h) (t.cast (le_of_eq h)) xs = boolean_realize_bounded_term v t xs :=
by {subst h, simp }

@[simp] lemma boolean_realize_bounded_term_bd_app
  {n l} (t : bounded_preterm L n (l+1)) (s : bounded_term L n) (xs : dvector S n)
  (xs' : dvector S l) :
  boolean_realize_bounded_term xs (bd_app t s) xs' =
  boolean_realize_bounded_term xs t (boolean_realize_bounded_term xs s ([])::xs') :=
by refl

@[simp] lemma boolean_realize_closed_term_bd_apps
  {l} (t : closed_preterm L l) (ts : dvector (closed_term L) l) :
  boolean_realize_closed_term S (bd_apps t ts) =
  boolean_realize_bounded_term ([]) t (ts.map (λt', boolean_realize_bounded_term ([]) t' ([]))) :=
begin
  induction ts generalizing t, refl, apply ts_ih (bd_app t ts_x)
end

lemma boolean_realize_bounded_term_bd_apps
  {n l} (xs : dvector S n) (t : bounded_preterm L n l) (ts : dvector (bounded_term L n) l) :
  boolean_realize_bounded_term xs (bd_apps t ts) ([]) =
  boolean_realize_bounded_term xs t (ts.map (λt, boolean_realize_bounded_term xs t ([]))) :=
begin
  induction ts generalizing t, refl, apply ts_ih (bd_app t ts_x)
end

@[simp] lemma boolean_realize_cast_bounded_term {n m} {h : n ≤ m} {t : bounded_term L n} {v : dvector S m} :
boolean_realize_bounded_term v (t.cast h) dvector.nil = boolean_realize_bounded_term (v.trunc n h) t dvector.nil :=
begin
  revert t, apply bounded_term.rec,
  {intro k, simp only [dvector.trunc_nth, fol.bounded_preterm.cast, fol.boolean_realize_bounded_term, dvector.nth, dvector.trunc], refl},
  {simp[boolean_realize_bounded_term_bd_apps], intros, congr' 1, apply dvector.map_congr_pmem,
  exact ih_ts}
end

/- When realizing a closed term, we can replace the realizing dvector with [] -/
@[simp] lemma boolean_realize_closed_term_v_irrel {n} {v : dvector S n} {t : bounded_term L 0} : boolean_realize_bounded_term v (t.cast (nat.zero_le n)) ([]) = boolean_realize_closed_term S t :=
  by simp[boolean_realize_cast_bounded_term]

lemma boolean_realize_bounded_term_subst_lift' {n} (v : dvector S n) (x : S) :
  ∀{l} (t : bounded_preterm L n l) (xs : dvector S l),
  boolean_realize_bounded_term (x::v) (t ↑' 1 # 0) xs = boolean_realize_bounded_term v t xs
| _ &k          [] :=
  begin
    have : 0 < k.val + 1, from lt_succ_of_le (nat.zero_le _), simp*, refl
  end
| _ (bd_func f)    xs := by refl
| _ (bd_app t₁ t₂) xs := by { dsimp, simp* }

@[simp] lemma boolean_realize_bounded_term_subst_lift {n} (v : dvector S n) (x : S)
  {l} (t : bounded_preterm L n l) (xs : dvector S l) :
  boolean_realize_bounded_term (x::v) (t ↑ 1) xs = boolean_realize_bounded_term v t xs :=
boolean_realize_bounded_term_subst_lift' v x t xs

/- this is the same as boolean_realize_bounded_term, we should probably have a common generalization of this definition -/
-- @[simp] def substitute_bounded_term {n n'} (v : dvector (bounded_term n') n) :
--   ∀{l} (t : bounded_term L n l, bounded_preterm L n' l
-- | _ _ &k          := v.nth k hk
-- | _ _ (bd_func f)             := bd_func f
-- | _ _ (bd_app t₁ t₂) := bd_app (substitute_bounded_term ht₁) $ substitute_bounded_term ht₂

-- def substitute_bounded_term {n n' l} (t : bounded_preterm L n l)
--   (v : dvector (bounded_term n') n) : bounded_preterm L n' l :=
-- substitute_bounded_term v t.snd

@[simp] def boolean_realize_bounded_formula :
  ∀{n l} (v : dvector S n) (f : bounded_preformula L n l) (xs : dvector S l), β
| _ _ v bd_falsum       xs := ⊥
| _ _ v (t₁ ≃ t₂)       xs := S.eq (boolean_realize_bounded_term v t₁ xs) (boolean_realize_bounded_term v t₂ xs)
| _ _ v (bd_rel R)      xs := S.rel_map R xs
| _ _ v (bd_apprel f t) xs := boolean_realize_bounded_formula v f $ boolean_realize_bounded_term v t ([])::xs
| _ _ v (f₁ ⟹ f₂)      xs := boolean_realize_bounded_formula v f₁ xs ⇒ boolean_realize_bounded_formula v f₂ xs
| _ _ v (∀' f)          xs := ⨅(x : S), boolean_realize_bounded_formula (x::v) f xs

notation S`[`:95 f ` ;; `:95 v ` ;; `:90 xs `]`:0 := @fol.boolean_realize_bounded_formula _ S _ _ v f xs
notation S`[`:95 f ` ;; `:95 v `]`:0 := @fol.boolean_realize_bounded_formula _ S _ 0 v f (dvector.nil)

@[reducible] def boolean_realize_sentence (S : bStructure L β) (f : sentence L) : β :=
boolean_realize_bounded_formula ([] : dvector S 0) f ([])

notation `⟦`:max f `⟧[` S `]`:0 := boolean_realize_sentence S f

lemma boolean_realize_bounded_formula_eq : ∀{n} {v₁ : dvector S n} {v₂ : ℕ → S}
  (hv : ∀k (hk : k < n), v₂ k = v₁.nth k hk) {l} (t : bounded_preformula L n l)
  (xs : dvector S l), boolean_realize_formula v₂ t.fst xs = boolean_realize_bounded_formula v₁ t xs
| _ _ _ hv _ bd_falsum       xs := by refl
| _ _ _ hv _ (t₁ ≃ t₂)       xs := by dsimp; congr' 1; apply boolean_realize_bounded_term_eq hv
| _ _ _ hv _ (bd_rel R)      xs := by refl
| _ _ _ hv _ (bd_apprel f t) xs :=
  by dsimp; simp [boolean_realize_bounded_term_eq hv, boolean_realize_bounded_formula_eq hv]
| _ _ _ hv _ (f₁ ⟹ f₂)      xs :=
  by dsimp; simp [boolean_realize_bounded_formula_eq hv]
| _ _ _ hv _ (∀' f)          xs :=
  begin
    apply congr_arg infi; apply funext, intro x, apply boolean_realize_bounded_formula_eq,
    intros k hk, cases k, refl, apply hv
  end

lemma boolean_realize_bounded_formula_eq' {L : Language} {S : bStructure L β} {n}
  {v₁ : dvector S n} (x : S) {l} (t : bounded_preformula L n l)
  (xs : dvector S l) :
    boolean_realize_bounded_formula v₁ t xs = boolean_realize_formula (λ k, if h : k < n then v₁.nth k h else x) t.fst xs :=
by { symmetry, apply boolean_realize_bounded_formula_eq, intros, rw [dif_pos] }

lemma boolean_realize_bounded_term_eq' {L : Language} {S : bStructure L β} {n}
  {v₁ : dvector S n} (x : S) {l} (t : bounded_preterm L n l)
  (xs : dvector S l) :
    boolean_realize_bounded_term v₁ t xs = boolean_realize_term (λ k, if h : k < n then v₁.nth k h else x) t.fst xs :=
by { symmetry, apply boolean_realize_bounded_term_eq, intros, rw [dif_pos] }

lemma boolean_realize_bounded_formula_congr {n l} (H_nonempty : nonempty S) (v₁ v₂ : dvector S n) (f : bounded_preformula L n l) (xs : dvector S l) : ((⨅(m : fin n), S.eq (v₁.nth m (m.is_lt)) (v₂.nth m m.is_lt)) ⊓ boolean_realize_bounded_formula v₁ f xs : β) ≤ (boolean_realize_bounded_formula v₂ f xs) :=
begin
  tactic.unfreeze_local_instances, cases H_nonempty with x,
  rw [boolean_realize_bounded_formula_eq' x], rw[boolean_realize_bounded_formula_eq' x],
  let v := (λ (k : ℕ), dite (k < n) (dvector.nth v₁ k) (λ (h : ¬k < n), x)),
  let v' := (λ (k : ℕ), dite (k < n) (λ (h : k < n), dvector.nth v₂ k h) (λ (h : ¬k < n), x)),
  have := boolean_realize_formula_congr v v' (f.fst) xs, convert this using 2,
  { refine le_antisymm _ _,
    { tidy_context, bv_intro N,
      by_cases H_lt : N < n,
        { simp only [v,v',dif_pos H_lt], exact a ⟨N, ‹_›⟩ },
        { simp [v,v', dif_neg H_lt]  } },
    { tidy_context, bv_intro m, rcases m with ⟨m,Hm⟩,
      replace a := a m, dsimp [v,v'] at a, simpa only [dif_pos Hm] using a }}
end

-- lemma boolean_realize_bounded_formula_eq_of_fst : ∀{n} {v₁ w₁ : dvector S n}
--   {v₂ w₂ : ℕ → S} (hv₁ : ∀ k (hk : k < n), v₁.nth k hk = v₂ k)
--   (hw₁ : ∀ k (hk : k < n), w₁.nth k hk = w₂ k) {l₁ l₂}
--   (t₁ : bounded_preformula L n l₁) (t₂ : bounded_preformula L n l₂) (xs₁ : dvector S l₁)
--   (xs₂ : dvector S l₂) (H : boolean_realize_formula v₂ t₁.fst xs₁ = boolean_realize_formula w₂ t₂.fst xs₂),
--   (boolean_realize_bounded_formula v₁ t₁ xs₁ = boolean_realize_bounded_formula w₁ t₂ xs₂) :=
--  by intros; simpa[(boolean_realize_bounded_formula_eq hv₁ t₁).symm, (boolean_realize_bounded_formula_eq hw₁ t₂).symm]

lemma boolean_realize_bounded_formula_irrel' {n n'} {v₁ : dvector S n} {v₂ : dvector S n'}
  (h : ∀m (hn : m < n) (hn' : m < n'), v₁.nth m hn = v₂.nth m hn')
  {l} (f : bounded_preformula L n l) (f' : bounded_preformula L n' l)
  (hf : f.fst = f'.fst) (xs : dvector S l) :
  boolean_realize_bounded_formula v₁ f xs = boolean_realize_bounded_formula v₂ f' xs :=
begin
  induction f generalizing n'; cases f'; injection hf with hf₁ hf₂,
  { refl },
  { simp [boolean_realize_bounded_term_irrel' h f_t₁ f'_t₁ hf₁,
          boolean_realize_bounded_term_irrel' h f_t₂ f'_t₂ hf₂] },
  { rw [hf₁], refl },
  { simp [boolean_realize_bounded_term_irrel' h f_t f'_t hf₂, f_ih _ h f'_f hf₁] },
  { dsimp, congr' 1, apply f_ih_f₁ _ h _ hf₁, apply f_ih_f₂ _ h _ hf₂ },
  { apply congr_arg infi; apply funext, intro x, apply f_ih _ _ _ hf₁, intros,
    cases m, refl, apply h }
end

lemma boolean_realize_bounded_formula_irrel {n} {v₁ : dvector S n}
  (f : bounded_formula L n) (f' : sentence L) (hf : f.fst = f'.fst) (xs : dvector S 0) :
  boolean_realize_bounded_formula v₁ f xs = ⟦f'⟧[S] :=
by cases xs; exact boolean_realize_bounded_formula_irrel'
  (by intros m hm hm'; exfalso; exact not_lt_zero m hm') f f' hf ([])

@[simp] lemma boolean_realize_bounded_formula_cast_eq_irrel {n m l} {h : n = m} {v : dvector S m} {f : bounded_preformula L n l} {xs : dvector S l} :
boolean_realize_bounded_formula v (f.cast_eq h) xs = boolean_realize_bounded_formula (v.cast h.symm) f xs :=
  by subst h; induction f; unfold bounded_preformula.cast_eq; finish


-- infix ` ⊨ᵇ `:51 := fol.boolean_realize_sentence -- input using \|= or \vDash, but not using \bModels
-- set_option pp.notation false
@[simp] lemma boolean_realize_sentence_false : ⟦(⊥ : sentence L)⟧[S] = (⊥ : β) :=
by refl

@[simp] lemma boolean_realize_sentence_imp {f₁ f₂ : sentence L} :
  ⟦f₁ ⟹ f₂⟧[S] = (⟦f₁⟧[S] ⇒ ⟦f₂⟧[S]) :=
by refl

@[simp] lemma boolean_realize_sentence_not {f : sentence L} :
  ⟦∼f⟧[S] = - (⟦f⟧[S]) :=
by simp [boolean_realize_sentence, bd_not]

lemma boolean_realize_sentence_dne {f : sentence L} :
  ⟦∼∼f⟧[S] = ⟦f⟧[S] :=
by simp [boolean_realize_sentence, bd_not]

@[simp] lemma boolean_realize_sentence_all {f : bounded_formula L 1} :
  ⟦∀'f⟧[S] = ⨅x : S, boolean_realize_bounded_formula([x]) f([]) :=
by refl

@[simp] lemma boolean_realize_bounded_formula_not {n} {v : dvector S n}
  {f : bounded_formula.{u} L n} :
  boolean_realize_bounded_formula v (∼f) ([]) = -boolean_realize_bounded_formula v f ([]) :=
by { simp [bd_not] }

@[simp] lemma boolean_realize_bounded_formula_or {n} {v : dvector S n}
  {f g : bounded_formula.{u} L n} :
  boolean_realize_bounded_formula v (f ⊔ g) ([]) =
  boolean_realize_bounded_formula v f ([]) ⊔ boolean_realize_bounded_formula v g ([]) :=
by { simp [bd_or, _root_.imp] }

@[simp] lemma boolean_realize_bounded_formula_and {n} {v : dvector S n}
  {f g : bounded_formula.{u} L n} :
  boolean_realize_bounded_formula v (f ⊓ g) ([]) =
  boolean_realize_bounded_formula v f ([]) ⊓ boolean_realize_bounded_formula v g ([]) :=
by { simp [bd_and, _root_.imp] }

@[simp] lemma boolean_realize_bounded_formula_ex {n} {v : dvector S n}
  {f : bounded_formula.{u} L (n+1)} :
  boolean_realize_bounded_formula v (∃' f) ([]) =
  ⨆(x : S), boolean_realize_bounded_formula (x::v) f ([]) :=
by { simp [bd_ex, compl_infi] }

lemma boolean_realize_bounded_sentence_ex {f : bounded_formula.{u} L 1} :
  boolean_realize_bounded_formula ([] : dvector S 0) (∃' f) ([]) =
  ⨆(x : S), boolean_realize_bounded_formula ([x]) f ([]) :=
boolean_realize_bounded_formula_ex

@[simp] lemma boolean_realize_bounded_formula_biimp {n} {v : dvector S n}
  {f g : bounded_formula.{u} L n} :
  boolean_realize_bounded_formula v (f ⇔ g) ([]) =
  (boolean_realize_bounded_formula v f ([]) ⟷ boolean_realize_bounded_formula v g ([])) :=
by {unfold bd_biimp, tidy}

lemma boolean_realize_bounded_formula_bd_apps_rel
  {n l} (xs : dvector S n) (f : bounded_preformula L n l) (ts : dvector (bounded_term L n) l) :
  boolean_realize_bounded_formula xs (bd_apps_rel f ts) ([]) =
  boolean_realize_bounded_formula xs f (ts.map (λt, boolean_realize_bounded_term xs t ([]))) :=
begin
  induction ts generalizing f, refl, apply ts_ih (bd_apprel f ts_x)
end

@[simp] lemma boolean_realize_cast_bounded_formula {n m} {h : n ≤ m} {f : bounded_formula L n} {v : dvector S m} :
boolean_realize_bounded_formula v (f.cast h) dvector.nil = boolean_realize_bounded_formula (v.trunc n h) f dvector.nil :=
begin
  by_cases n = m,
    by subst h; simp,
    have : n < m, by apply nat.lt_of_le_and_ne; repeat{assumption},
    apply boolean_realize_bounded_formula_irrel',
    {intros, simp},
    {simp}
end

@[simp] lemma boolean_realize_cast1_bounded_formula {n} {f : bounded_formula L n}
  {v : dvector S (n+1)} :
  boolean_realize_bounded_formula v f.cast1 dvector.nil =
  boolean_realize_bounded_formula (v.trunc n $ n.le_add_right 1) f dvector.nil :=
boolean_realize_cast_bounded_formula

lemma boolean_realize_sentence_bd_apps_rel'
  {l} (f : presentence L l) (ts : dvector (closed_term L) l) :
  ⟦bd_apps_rel f ts⟧[S] =
  boolean_realize_bounded_formula ([]) f (ts.map $ boolean_realize_closed_term S) :=
boolean_realize_bounded_formula_bd_apps_rel ([]) f ts

lemma boolean_realize_bd_apps_rel
  {l} (R : L.relations l) (ts : dvector (closed_term L) l) :
  ⟦bd_apps_rel (bd_rel R) ts⟧[S] = S.rel_map R (ts.map $ boolean_realize_closed_term S) :=
by apply boolean_realize_bounded_formula_bd_apps_rel ([]) (bd_rel R) ts

lemma boolean_realize_sentence_equal (t₁ t₂ : closed_term L) :
  ⟦t₁ ≃ t₂⟧[S] = S.eq (boolean_realize_closed_term S t₁) (boolean_realize_closed_term S t₂) :=
by refl

lemma boolean_realize_sentence_eq (v : ℕ → S) (f : sentence L) :
  boolean_realize_formula v f.fst ([]) = ⟦f⟧[S] :=
boolean_realize_bounded_formula_eq (λk hk, by exfalso; exact not_lt_zero k hk) f _

lemma bstatisfied_in_eq_boolean_realize_sentence [HS : nonempty S] (f : sentence L) :
  ⟦f.fst⟧[S]ᵤ = ⟦f⟧[S] :=
begin
  haveI : nonempty (ℕ → S) := HS.map (λ x n, x),
  simp [boolean_realize_formula_glb, boolean_realize_sentence_eq]
end

def forced_in (x : β) (S : bStructure L β) (f : sentence L) : Prop :=
x ≤ ⟦f⟧[S]

notation x ` ⊩[`:52 S `] `:0 f:52 := forced_in x S f

def all_forced_in (x : β) (S : bStructure L β) (T : Theory L) : Prop :=
x ≤ ⨅(f ∈ T), ⟦f⟧[S]

notation x ` ⊩[`:52 S `] `:0 T:52 := all_forced_in x S T

@[simp]lemma forced_in_not {f : sentence L} {b} : b ⊩[S] ∼∼f ↔ b ⊩[S] f :=
by {change _ ≤ _ ↔ _ ≤ _, simp}

-- lemma all_boolean_realize_sentence_axm {f : sentence L} {T : Theory L} :
--   ∀ (H : S ⊨ᵇ insert f T = ⊤), S ⊨ᵇ f = ⊤ ∧ S ⊨ᵇ T = ⊤ :=
-- sorry --λ H, ⟨by {apply H, exact or.inl rfl}, by {intros ψ hψ, apply H, exact or.inr hψ}⟩

-- @[simp] lemma all_boolean_realize_sentence_axm_rw {f : sentence L} {T : Theory L} : (S ⊨ᵇ insert f T) = ((S ⊨ᵇ f : β) ⊓ (S ⊨ᵇ T : β) : β) :=
-- begin
--   refine ⟨by apply all_boolean_realize_sentence_axm, _⟩, intro H,
--   rcases H with ⟨Hf, HT⟩, intros g Hg, rcases Hg with ⟨Hg1, Hg2⟩,
--   exact Hf, exact HT Hg
-- end

-- @[simp] lemma all_boolean_realize_sentence_singleton {f : sentence L} : S ⊨ᵇ {f} = S ⊨ᵇ f :=
--   ⟨by{intro H, apply H, exact or.inl rfl}, by {intros H g Hg, repeat{cases Hg}, assumption}⟩

variable (β)
def forced (T : Theory L) (f : sentence L) :=
∀{{S : bStructure L β}}, nonempty S → (⨅(f ∈ T), ⟦f⟧[S]) ⊩[S] f
variable {β}
notation T ` ⊨[`:51 β`] `:0 f := fol.forced β T f -- input using \|= or \vDash, but not using \bModels

def bsatisfied_of_forced {T : Theory L} {f : sentence L} (H : T ⊨[β] f) : T.fst ⊨ᵤ[β] f.fst :=
begin
  intros S v, rw [boolean_realize_sentence_eq],
  refine le_trans _ (H ⟨v 0⟩),
  rw [le_infi_iff], intro f, rw [le_infi_iff], intro hf,
  refine le_trans (infi_le _ f.fst) _,
  refine le_trans (infi_le _ (mem_image_of_mem _ hf)) _,
  apply le_of_eq, rw [boolean_realize_sentence_eq]
end

def forced_of_bsatisfied {T : Theory L} {f : sentence L} (H : T.fst ⊨ᵤ[β] f.fst) : T ⊨[β] f :=
begin
  intros S hS, induction hS with s, dsimp [forced_in],
  rw [←boolean_realize_sentence_eq (λ _, s)],
  refine le_trans _ (H S (λ _, s)),
  rw [le_infi_iff], intro f', rw [le_infi_iff], intro hf',
  rcases hf' with ⟨f', ⟨hf', rfl⟩⟩, rw [boolean_realize_sentence_eq],
  refine le_trans (infi_le _ f') (infi_le _ hf')
end

@[simp]lemma inf_axioms_top_of_models {S : bStructure L β} {T : Theory L} (H : ⊤ ⊩[S] T) :
  (⨅(f ∈ T), ⟦f⟧[S]) = ⊤ :=
by {apply top_unique, from le_trans H (by refl)}

lemma forced_absurd {S : bStructure L β} {T : Theory L} {f : sentence L} {Γ : β} (H₁ : Γ ⊩[S] f) (H₂ : Γ ⊩[S] ∼f) : Γ ⊩[S] bd_falsum :=
begin
  change Γ ≤ _, apply le_trans' H₁, apply le_trans,
  apply inf_le_inf, from H₂, refl, simp
end

--infix ` ⊨ᵇ `:51 := fol.forced -- input using \|= or \vDash, but not using \bModels

-- def all_forced (T T' : Theory L) := ∀(f ∈ T'), T ⊨ᵇ f
-- infix ` ⊨ᵇ `:51 := fol.all_ssatisfied -- input using \|= or \vDash, but not using \bModels


-- def ssatisfied_snot {f : sentence L} (hS : ¬(S ⊨ᵇ f)) : S ⊨ᵇ ∼ f :=
-- by exact hS

variable (β)
def bModel (T : Theory L) : Type* := Σ' (S : bStructure.{u v} L β), ⊤ ⊩[S] T
variable {β}

-- @[reducible] def bModel_ssatisfied {T : Theory L} (M : bModel β T) (ψ : sentence L) := M.fst ⊨ᵇ ψ

-- infix ` ⊨ᵇ `:51 := fol.bModel_ssatisfied -- input using \|= or \vDash, but not using \bModels

-- @[simp] lemma false_of_bModel_absurd {T : Theory L} (M : bModel β T) {ψ : sentence L} (h : M ⊨ᵇ ψ) (h' : M ⊨ᵇ ∼ψ) : false :=
-- by {unfold bModel_ssatisfied at *, simp[*,-h'] at h', exact h'}

theorem boolean_soundness {T : Theory L} {A : sentence L} (H : T ⊢ A) : T ⊨[β] A :=
forced_of_bsatisfied $ boolean_formula_soundness H

lemma unprovable_of_model_neg {T : Theory L} {f : sentence L} (S : bStructure L β) (H_model : ⊤ ⊩[S] T) [H_nonempty : nonempty S]
  {Γ : β} (H_nonzero : (⊥ : β) < Γ) (H : Γ ⊩[S] ∼f) : ¬ (T ⊢' f) :=
begin
  intro Hp, refine absurd H_nonzero (not_lt_of_le (forced_absurd _ H : Γ ⊩[S] (bd_falsum))),
  from T, have := boolean_soundness (sprovable_of_provable (classical.choice Hp)) H_nonempty,
  rw inf_axioms_top_of_models at this, from le_trans le_top ‹_›, from ‹_›
end

lemma boolean_realize_subst_preterm {n l} (t : bounded_preterm L (n+1) l)
  (xs : dvector S l) (s : closed_term L) (v : dvector S n) :
  boolean_realize_bounded_term v (substmax_bounded_term t s) xs =
  boolean_realize_bounded_term (v.concat (boolean_realize_closed_term S s)) t xs :=
begin
  induction t,
  { by_cases h : t.1 < n,
    { rw [substmax_var_lt t s h], dsimp,
      simp only [dvector.map_nth, dvector.concat_nth _ _ _ _ h, dvector.nth'],  },
    { have h' := le_antisymm (le_of_lt_succ t.2) (le_of_not_gt h), simp [h', dvector.nth'],
      rw [substmax_var_eq t s h'],
      apply boolean_realize_bounded_term_irrel, simp }},
  { refl },
  { dsimp, rw [substmax_bounded_term_bd_app], dsimp, rw [t_ih_s ([]), t_ih_t] }
end

lemma boolean_realize_subst_term {n} (v : dvector S n) (s : closed_term L)
  (t : bounded_term L (n+1))  :
  boolean_realize_bounded_term v (substmax_bounded_term t s) ([]) =
  boolean_realize_bounded_term (v.concat (boolean_realize_closed_term S s)) t ([]) :=
by apply boolean_realize_subst_preterm t ([]) s v

lemma boolean_realize_sentence_bd_alls {f : bounded_formula L n} {S : bStructure L β} :
  boolean_realize_sentence S (bd_alls n f) =
  ⨅ xs : dvector S n, boolean_realize_bounded_formula xs f ([]) :=
begin
  induction n,
  { simp [-alls'_alls], apply le_antisymm,
    { rw [le_infi_iff], intro xs, cases xs, refl },
    { exact infi_le _ ([]) }},
  { rw [bd_alls, n_ih], --have := @n_ih (∀' f),
    apply le_antisymm,
    { rw [le_infi_iff], intro xs, cases xs with _ x xs,
      refine le_trans (infi_le _ xs) _,
      exact infi_le _ x },
    { rw [le_infi_iff], intro xs, rw [boolean_realize_bounded_formula, le_infi_iff], intro x,
      exact infi_le _ (x::xs) }}
end

end bfol

section consis_lemma
variables {L : Language} {β : Type u}

lemma consis_of_exists_bmodel [nontrivial_complete_boolean_algebra β] {T : Theory L} {S : bStructure L β} [h_nonempty : nonempty S] (H : ⊤ ⊩[S] T) :
  is_consistent T :=
begin
  intro H_inconsis,
  suffices forces_false : ⊤ ⊩[S] bd_falsum,
    from absurd (nontrivial.bot_lt_top) (not_lt_of_le forces_false),
  convert (boolean_soundness (classical.choice H_inconsis) (h_nonempty)),
  finish
end

end consis_lemma

variables {β : Type*} [complete_boolean_algebra β]

@[simp] lemma subst0_bounded_formula_not {L : Language} {n} (f : bounded_formula L (n+1))
  (s : bounded_term L n) : (∼f)[s/0] = ∼(f[s/0]) :=
by { ext, simp [bd_not] }

@[simp] lemma subst0_bounded_formula_and {L : Language} {n} (f g : bounded_formula L (n+1))
  (s : bounded_term L n) : (f ⊓ g)[s/0] = (f[s/0] ⊓ g[s/0]) :=
by { ext, simp[bd_and, bd_not] }

-- --TODO(floris)
-- lemma realize_subst_bt {L : Language} {S : bStructure L β} : ∀{n n' l}
--   (t : bounded_preterm L (n+n'+1) l)
--   (s : bounded_term L n') (v : dvector S n) (v' : dvector S n') (v'' : dvector S l),
--   boolean_realize_bounded_term ((v.append v').cast (add_comm n' n))
--     (subst_bounded_term t s) v'' =
--   boolean_realize_bounded_term
--     (((v.concat $ boolean_realize_bounded_term v' s ([])).append v').cast $
--       (by simp only [add_comm, add_right_inj, add_left_comm])) t v'' :=
-- begin
--   intros, induction t,
--   { apply decidable.lt_by_cases t.1 n; intro h, simp [h, subst_bounded_term],  repeat {sorry} },
--   { sorry },
--   { sorry },
-- end

-- lemma realize_subst_bf {L : Language} {S : bStructure L β} : ∀{n n' n'' l}
--   (f : bounded_preformula L n'' l)
--   (s : bounded_term L n') (v : dvector S n) (v' : dvector S n') (v'' : dvector S l)
--   (h : n+n'+1 = n''),
--   boolean_realize_bounded_formula ((v.append v').cast (add_comm n' n))
--     (subst_bounded_formula f s h) v'' =
--   boolean_realize_bounded_formula
--     (((v.concat $ boolean_realize_bounded_term v' s ([])).append v').cast $
--       eq.trans (by simp only [add_comm, add_right_inj, add_left_comm]) h) f v'' :=
-- begin
--   intros, induction f generalizing n n'; induction h,
--   { refl },
--   { simp [realize_subst_bt] },
--   { refl },
--   { simp [realize_subst_bt, f_ih] },
--   { simp [f_ih_f₁, f_ih_f₂], },
--   { simp, congr, ext, sorry /-have := f_ih ([]) s v,-/ },
-- end

-- lemma realize_subst0_bf {L : Language} {n} (f : bounded_formula L (n+1)) (t : bounded_term L n)
--   {S : bStructure L β} (v : dvector S n) :
--   boolean_realize_bounded_formula v (f[t/0]) ([]) =
--   boolean_realize_bounded_formula (boolean_realize_bounded_term v t ([])::v) f ([]) :=
-- by { convert realize_subst_bf f t ([]) v ([]) _ using 1, simp [subst0_bounded_formula], refl }

-- lemma realize_substmax_bf {L : Language} {n} (f : bounded_formula L (n+1)) (t : closed_term L)
--   {S : bStructure L β} (v : dvector S n) :
--   boolean_realize_bounded_formula v (substmax_bounded_formula f t) ([]) =
--   boolean_realize_bounded_formula (v.concat $ boolean_realize_closed_term S t) f ([]) :=
-- by { convert realize_subst_bf f t v ([]) ([]) _, rw [cast_append_nil], simp, }

lemma boolean_realize_bounded_formula_insert_lift {L : Language} {S : bStructure L β}
  {n l} (v : dvector S n) (x : S) (m : ℕ) (hm : m ≤ n)
  (f : bounded_preformula L n l) (xs : dvector S l) :
    boolean_realize_bounded_formula (v.insert x m) (f ↑' 1 # m) xs =
    boolean_realize_bounded_formula v f xs :=
begin
  rw [boolean_realize_bounded_formula_eq' x, boolean_realize_bounded_formula_eq' x], simp,
  convert boolean_realize_formula_subst_lift _ x _ _ _, ext k,
  by_cases hk : k < n + 1,
  { simp [hk],
    apply decidable.lt_by_cases m k; intro hm'; simp [hm'],
    { have hk2 : k - 1 < n, from (nat.sub_lt_right_iff_lt_add (nat.one_le_of_lt hm')).mpr hk,
      simp [hk2] },
    have hk2 : k < n, from lt_of_lt_of_le hm' hm,
    simp [hk2, dvector.insert_nth_lt x v hk2 hk hm'] },
  { have h2 : ¬k - 1 < n, from mt nat.lt_add_of_sub_lt_right hk,
    have h3 : m < k, from lt_of_le_of_lt hm (lt_of_not_ge $ mt nat.lt_succ_of_le hk),
    simp [hk, h2, h3] }
end

@[simp] lemma boolean_realize_formula_insert_lift2 {L : Language} {S : bStructure L β}
  {n} (v : dvector S n) (x y z : S) (f : bounded_formula L (n+2)) :
    boolean_realize_bounded_formula (x :: y :: z :: v) (f ↑' 1 # 2) ([]) =
    boolean_realize_bounded_formula (x :: y :: v) f ([]) :=
by { convert boolean_realize_bounded_formula_insert_lift _ z 2 (le_add_left (le_refl 2)) f ([]),
     simp }

lemma boolean_realize_subst_formula0 {L : Language} {n} (S : bStructure L β) [nonempty S]
  (f : bounded_formula L (n+1)) (t : bounded_term L n) (v : dvector S n) :
  boolean_realize_bounded_formula v (f[t/0]) ([]) =
  boolean_realize_bounded_formula (boolean_realize_bounded_term v t ([])::v) f ([]) :=
begin
  have := _inst_2, cases this with y, rw [boolean_realize_bounded_formula_eq' y, boolean_realize_bounded_formula_eq' y, boolean_realize_bounded_term_eq' y], simp,
  convert (boolean_realize_formula_subst0 _ _ _ _).symm, ext k,
  simp [subst_realize, not_lt_zero],
  by_cases hk : k < n + 1,
  { cases k with k,
    { simp },
    { have h2k : k < n, from lt_of_succ_lt_succ hk,
      simp [hk, h2k] }},
  { have h2k : 0 < k, from lt_of_lt_of_le (zero_lt_succ n) (le_of_not_gt hk),
    have h3k : ¬k - 1 < n, from mt nat.lt_add_of_sub_lt_right hk,
    simp [hk, h2k, h3k] }
end
end fol


-- #exit
-- lemma boolean_realize_subst_formula (S : bStructure L β) {n} (f : bounded_formula L (n+1))
--   (t : closed_term L) (v : dvector S n) :
--   boolean_realize_bounded_formula v (substmax_bounded_formula f t) ([]) =
--   boolean_realize_bounded_formula (v.concat (boolean_realize_closed_term S t)) f ([]) :=
-- begin
--   revert n f v, refine bounded_formula.rec1 _ _ _ _ _; intros,
--   { simp },
--   {sorry},
--   { rw [substmax_bounded_formula_bd_apps_rel, boolean_realize_bounded_formula_bd_apps_rel,
--         boolean_realize_bounded_formula_bd_apps_rel],
--     simp [ts.map_congr (realize_subst_term _ _)], sorry },
--   {sorry
--  -- apply imp_congr, apply ih₁ v, apply ih₂ v
--   },
--   { simp, apply congr_arg infi; apply funext, intro x, apply ih (x::v) }
-- end

-- /-- Given a bModel M ⊨ᵇ T with M ⊨ᵇ ¬ ψ, ¬ T ⊨ᵇ ψ--/
-- @[simp] lemma not_satisfied_of_bModel_not {T : Theory L} {ψ : sentence L} (M : bModel β T) (hM : M ⊨ᵇ ∼ψ) (h_nonempty : nonempty M.fst): ¬ T ⊨ᵇ ψ :=
-- begin
--   intro H, suffices : M ⊨ᵇ ψ, exact false_of_bModel_absurd M this hM,
--   exact H h_nonempty M.snd
-- end

-- --infix ` ⊨ᵇ `:51 := fol.ssatisfied -- input using \|= or \vDash, but not using \bModels

-- /- consistent theories -/
-- def is_consistent (T : Theory L) := ¬(T ⊢' (⊥ : sentence L))

-- protected def is_consistent.intro {T : Theory L} (H : ¬ T ⊢' (⊥ : sentence L)) : is_consistent T :=
-- H

-- protected def is_consistent.elim {T : Theory L} (H : is_consistent T) : ¬ T ⊢' (⊥ : sentence L)
-- | H' := H H'

-- lemma consis_not_of_not_provable {L} {T : Theory L} {f : sentence L} :
--   ¬ T ⊢' f → is_consistent (T ∪ {∼f}) :=
-- begin
--   intros h₁ h₂, cases h₂ with h₂, simp only [*, set.union_singleton] at h₂,
--   apply h₁, exact ⟨sfalsumE h₂⟩
-- end

-- /- complete theories -/
-- def is_complete (T : Theory L) :=
-- is_consistent T ∧ ∀(f : sentence L), f ∈ T ∨ ∼ f ∈ T

-- def mem_of_sprf {T : Theory L} (H : is_complete T) {f : sentence L} (Hf : T ⊢ f) : f ∈ T :=
-- begin
--   cases H.2 f, exact h, exfalso, apply H.1, constructor, refine impE _ _ Hf, apply saxm h
-- end

-- def mem_of_sprovable {T : Theory L} (H : is_complete T) {f : sentence L} (Hf : T ⊢' f) : f ∈ T :=
-- by destruct Hf; exact mem_of_sprf H

-- def sprovable_of_sprovable_or {T : Theory L} (H : is_complete T) {f₁ f₂ : sentence L}
--   (H₂ : T ⊢' f₁ ⊔ f₂) : (T ⊢' f₁) ∨ T ⊢' f₂ :=
-- begin
--   cases H.2 f₁ with h h, { left, exact ⟨saxm h⟩ },
--   cases H.2 f₂ with h' h', { right, exact ⟨saxm h'⟩ },
--   exfalso, destruct H₂, intro H₂, apply H.1, constructor,
--   apply orE H₂; refine impE _ _ axm1; apply weakening1; apply axm;
--     [exact mem_image_of_mem _ h, exact mem_image_of_mem _ h']
-- end

-- def impI_of_is_complete {T : Theory L} (H : is_complete T) {f₁ f₂ : sentence L}
--   (H₂ : T ⊢' f₁ → T ⊢' f₂) : T ⊢' f₁ ⟹ f₂ :=
-- begin
--   apply impI', cases H.2 f₁,
--   { apply weakening1', apply H₂, exact ⟨saxm h⟩ },
--   apply falsumE', apply weakening1',
--   apply impE' _ (weakening1' ⟨by apply saxm h⟩) ⟨axm1⟩
-- end

-- def notI_of_is_complete {T : Theory L} (H : is_complete T) {f : sentence L}
--   (H₂ : ¬T ⊢' f) : T ⊢' ∼f :=
-- begin
--   apply @impI_of_is_complete _ T H f ⊥,
--   intro h, exfalso, exact H₂ h
-- end

-- def has_enough_constants (T : Theory L) :=
-- ∃(C : Π(f : bounded_formula L 1), L.constants),
-- ∀(f : bounded_formula L 1), T ⊢' ∃' f ⟹ f[bd_const (C f)/0]

-- lemma has_enough_constants.intro {L : Language} (T : Theory L)
--   (H : ∀(f : bounded_formula L 1), ∃ c : L.constants, T ⊢' ∃' f ⟹ f[bd_const c/0]) :
--   has_enough_constants T :=
-- classical.axiom_of_choice H

-- def find_counterexample_of_henkin {T : Theory L} (H₁ : is_complete T) (H₂ : has_enough_constants T)
--   (f : bounded_formula L 1) (H₃ : ¬ T ⊢' ∀' f) : ∃(t : closed_term L), T ⊢' ∼ f[t/0] :=
-- begin
--   induction H₂ with C HC,
--   refine ⟨bd_const (C (∼ f)), _⟩, dsimp [sprovable] at HC,
--   apply (HC _).map2 (impE _),
--   apply nonempty.map ex_not_of_not_all, apply notI_of_is_complete H₁ H₃
-- end

-- variables (T : Theory L) (H₁ : is_complete T) (H₂ : has_enough_constants T)
-- def term_rel (t₁ t₂ : closed_term L) : β := T ⊢' t₁ ≃ t₂

-- def term_setoid : setoid $ closed_term L :=
-- ⟨term_rel T, λt, ⟨ref _ _⟩, λt t' H, H.map symm, λt₁ t₂ t₃ H₁ H₂, H₁.map2 trans H₂⟩
-- local attribute [instance] term_setoid

-- def term_bModel' : Type u :=
-- quotient $ term_setoid T
-- -- set_option pp.all true
-- -- #print term_setoid
-- -- set_option trace.class_instances true

-- def term_bModel_fun' {l} (t : closed_preterm L l) (ts : dvector (closed_term L) l) : term_bModel' T :=
-- @quotient.mk _ (term_setoid T) $ bd_apps t ts

-- -- def equal_preterms_trans {T : set (formula L)} : ∀{l} {t₁ t₂ t₃ : preterm L l}
-- --   (h₁₂ : equal_preterms T t₁ t₂) (h₂₃ : equal_preterms T t₂ t₃), equal_preterms T t₁ t₃

-- variable {T}
-- def term_bModel_fun_eq {l} (t t' : closed_preterm L (l+1)) (x x' : closed_term L)
--   (Ht : equal_preterms T.fst t.fst t'.fst) (Hx : T ⊢ x ≃ x') (ts : dvector (closed_term L) l) :
--   term_bModel_fun' T (bd_app t x) ts = term_bModel_fun' T (bd_app t' x') ts :=
-- begin
--   induction ts generalizing x x',
--   { apply quotient.sound, refine ⟨trans (app_congr t.fst Hx) _⟩, apply Ht ([x'.fst]) },
--   { apply ts_ih, apply equal_preterms_app Ht Hx, apply ref }
-- end

-- variable (T)
-- def term_bModel_fun {l} (t : closed_preterm L l) (ts : dvector (term_bModel' T) l) : term_bModel' T :=
-- begin
--   refine ts.quotient_lift (term_bModel_fun' T t) _, clear ts,
--   intros ts ts' hts,
--   induction hts,
--   { refl },
--   { apply (hts_ih _).trans, induction hts_hx with h, apply term_bModel_fun_eq,
--     refl, exact h }
-- end

-- def term_bModel_rel' {l} (f : presentence L l) (ts : dvector (closed_term L) l) : β :=
-- T ⊢' bd_apps_rel f ts

-- variable {T}
-- def term_bModel_rel_iff {l} (f f' : presentence L (l+1)) (x x' : closed_term L)
--   (Ht : equiv_preformulae T.fst f.fst f'.fst) (Hx : T ⊢ x ≃ x') (ts : dvector (closed_term L) l) :
--   term_bModel_rel' T (bd_apprel f x) ts = term_bModel_rel' T (bd_apprel f' x') ts :=
-- begin
--   induction ts generalizing x x',
--   { apply iff.trans (apprel_congr' f.fst Hx),
--     apply iff_of_biimp, have := Ht ([x'.fst]), exact ⟨this⟩ },
--   { apply ts_ih, apply equiv_preformulae_apprel Ht Hx, apply ref }
-- end

-- variable (T)
-- def term_bModel_rel {l} (f : presentence L l) (ts : dvector (term_bModel' T) l) : β :=
-- begin
--   refine ts.quotient_lift (term_bModel_rel' T f) _, clear ts,
--   intros ts ts' hts,
--   induction hts,
--   { refl },
--   { apply (hts_ih _).trans, induction hts_hx with h, apply βext, apply term_bModel_rel_iff,
--     refl, exact h }
-- end

-- def term_bModel : bStructure L β :=
-- ⟨term_bModel' T,
--  λn, term_bModel_fun T ∘ bd_func,
--  λn, term_bModel_rel T ∘ bd_rel⟩

-- @[reducible] def term_mk : closed_term L → term_bModel β T :=
-- @quotient.mk _ $ term_setoid T

-- -- lemma realize_bounded_preterm_term_bModel {l n} (ts : dvector (closed_term L) l)
-- --   (t : bounded_preterm L l n) (ts' : dvector (closed_term L) n) :
-- --   boolean_realize_bounded_term (ts.map term_mk) t (ts'.map term_mk) =
-- --   (term_mk _) :=
-- -- begin
-- --   induction t with t ht,
-- --   sorry
-- -- end

-- variable {T}
-- lemma realize_closed_preterm_term_bModel {l} (ts : dvector (closed_term L) l) (t : closed_preterm L l) :
--   boolean_realize_bounded_term ([]) t (ts.map $ term_mk T) = (term_mk T (bd_apps t ts)) :=
-- begin
--   induction t,
--   { apply t.fin_zero_elim },
--   { apply dvector.quotient_beta },
--   { rw [boolean_realize_bounded_term_bd_app],
--     have := t_ih_s ([]), dsimp at this, rw this,
--     apply t_ih_t (t_s::ts) }
-- end

-- @[simp] lemma boolean_realize_closed_term_term_bModel (t : closed_term L) :
--   boolean_realize_closed_term (term_bModel β T) t = term_mk T t :=
-- by apply realize_closed_preterm_term_bModel ([]) t
-- /- below we try to do this directly using bounded_term.rec -/
-- -- begin
-- --   revert t, refine bounded_term.rec _ _; intros,
-- --   { apply k.fin_zero_elim },
-- --   --{ apply dvector.quotient_beta },
-- --   {

-- --     --exact dvector.quotient_beta _ _ ts,
-- --     rw [boolean_realize_bounded_term_bd_app],
-- --     have := t_ih_s ([]), dsimp at this, rw this,
-- --     apply t_ih_t (t_s::ts) }
-- -- end


-- lemma boolean_realize_subst_preterm {n l} (t : bounded_preterm L (n+1) l)
--   (xs : dvector S l) (s : closed_term L) (v : dvector S n) :
--   boolean_realize_bounded_term v (substmax_bounded_term t s) xs =
--   boolean_realize_bounded_term (v.concat (boolean_realize_closed_term S s)) t xs :=
-- begin
--   induction t,
--   { by_cases h : t.1 < n,
--     { rw [substmax_var_lt t s h], dsimp,
--       simp only [dvector.map_nth, dvector.concat_nth _ _ _ _ h, dvector.nth'],  },
--     { have h' := le_antisymm (le_of_lt_succ t.2) (le_of_not_gt h), simp [h', dvector.nth'],
--       rw [substmax_var_eq t s h'],
--       apply boolean_realize_bounded_term_irrel, simp }},
--   { refl },
--   { dsimp, rw [substmax_bounded_term_bd_app], dsimp, rw [t_ih_s ([]), t_ih_t] }
-- end

-- lemma boolean_realize_subst_term {n} (v : dvector S n) (s : closed_term L)
--   (t : bounded_term L (n+1))  :
--   boolean_realize_bounded_term v (substmax_bounded_term t s) ([]) =
--   boolean_realize_bounded_term (v.concat (boolean_realize_closed_term S s)) t ([]) :=
-- by apply boolean_realize_subst_preterm t ([]) s v

-- lemma boolean_realize_subst_formula (S : bStructure L β) {n} (f : bounded_formula L (n+1))
--   (t : closed_term L) (v : dvector S n) :
--   boolean_realize_bounded_formula v (substmax_bounded_formula f t) ([]) =
--   boolean_realize_bounded_formula (v.concat (boolean_realize_closed_term S t)) f ([]) :=
-- begin
--   revert n f v, refine bounded_formula.rec1 _ _ _ _ _; intros,
--   { simp },
--   { apply eq.congr, exact realize_subst_term v t t₁, exact realize_subst_term v t t₂ },
--   { rw [substmax_bounded_formula_bd_apps_rel, boolean_realize_bounded_formula_bd_apps_rel,
--         boolean_realize_bounded_formula_bd_apps_rel],
--     simp [ts.map_congr (realize_subst_term _ _)] },
--   { apply imp_congr, apply ih₁ v, apply ih₂ v },
--   { simp, apply congr_arg infi; apply funext, intro x, apply ih (x::v) }
-- end

-- lemma boolean_realize_subst_formula0 (S : bStructure L β) (f : bounded_formula L 1) (t : closed_term L) :
--   S ⊨ᵇ f[t/0] = boolean_realize_bounded_formula ([boolean_realize_closed_term S t]) f ([]) :=
-- iff.trans (by rw [substmax_eq_subst0_formula]) (by apply boolean_realize_subst_formula S f t ([]))

-- lemma term_bModel_subst0 (f : bounded_formula L 1) (t : closed_term L) :
--   term_bModel β T ⊨ᵇ f[t/0] = boolean_realize_bounded_formula ([term_mk T t]) f ([]) :=
-- (boolean_realize_subst_formula0 (term_bModel β T) f t).trans (by simp)

-- include H₂
-- instance nonempty_term_bModel : nonempty $ term_bModel β T :=
-- begin
--   induction H₂ with C, exact ⟨term_mk T (bd_const (C (&0 ≃ &0)))⟩
-- end

-- include H₁
-- def term_bModel_ssatisfied_iff {n} : ∀{l} (f : presentence L l)
--   (ts : dvector (closed_term L) l) (h : count_quantifiers f.fst < n),
--   T ⊢' bd_apps_rel f ts = term_bModel β T ⊨ᵇ bd_apps_rel f ts :=
-- begin
--   refine nat.strong_induction_on n _, clear n,
--   intros n n_ih l f ts hn,
--   have : {f' : preformula L l // f.fst = f' } := ⟨f.fst, rfl⟩,
--   cases this with f' hf, induction f'; cases f; injection hf with hf₁ hf₂,
--   { simp, exact H₁.1.elim },
--   { simp, refine iff.trans _ (boolean_realize_sentence_equal f_t₁ f_t₂).symm, simp [term_mk], refl },
--   { refine iff.trans _ (boolean_realize_bd_apps_rel _ _).symm,
--     dsimp [term_bModel, term_bModel_rel],
--     rw [ts.map_congr boolean_realize_closed_term_term_bModel, dvector.quotient_beta], refl },
--   { apply f'_ih f_f (f_t::ts) _ hf₁, simp at hn ⊢, exact hn },
--   { have ih₁ := f'_ih_f₁ f_f₁ ([]) (lt_of_le_of_lt (nat.le_add_right _ _) hn) hf₁,
--     have ih₂ := f'_ih_f₂ f_f₂ ([]) (lt_of_le_of_lt (nat.le_add_left _ _) hn) hf₂, cases ts,
--     split; intro h,
--     { intro h₁, apply ih₂.mp, apply h.map2 (impE _), refine ih₁.mpr h₁ },
--     { simp at h, simp at ih₁, rw [←ih₁] at h, simp at ih₂, rw [←ih₂] at h,
--       exact impI_of_is_complete H₁ h }},
--   { cases ts, split; intro h,
--     { simp at h ⊢,
--       apply quotient.ind, intro t,
--       apply (term_bModel_subst0 f_f t).mp,
--       cases n with n, { exfalso, exact not_lt_zero _ hn },
--       refine (n_ih n (lt.base n) (f_f[t/0]) ([]) _).mp (h.map _),
--       simp, exact lt_of_succ_lt_succ hn,
--       rw [bd_apps_rel_zero, subst0_bounded_formula_fst],
--       exact allE₂ _ _ },
--     { apply classical.by_contradiction, intro H,
--       cases find_counterexample_of_henkin H₁ H₂ f_f H with t ht,
--       apply H₁.left, apply impE' _ ht,
--       cases n with n, { exfalso, exact not_lt_zero _ hn },
--       refine (n_ih n (lt.base n) (f_f[t/0]) ([]) _).mpr _,
--       { simp, exact lt_of_succ_lt_succ hn },
--       exact (term_bModel_subst0 f_f t).mpr (h (term_mk T t)) }},
-- end

-- def term_bModel_ssatisfied : term_bModel β T ⊨ᵇ T :=
-- begin
--   intros f hf, apply (term_bModel_ssatisfied_iff H₁ H₂ f ([]) (lt.base _)).mp, exact ⟨saxm hf⟩
-- end

-- -- completeness for complete theories with enough constants
-- lemma completeness' {f : sentence L} (H : T ⊨ᵇ f) : T ⊢' f :=
-- begin
--   apply (term_bModel_ssatisfied_iff H₁ H₂ f ([]) (lt.base _)).mpr,
--   apply H, exact fol.nonempty_term_bModel H₂,
--   apply term_bModel_ssatisfied H₁ H₂,
-- end
-- omit H₁ H₂

-- def Th (S : bStructure L β) : Theory L := { f : sentence L | S ⊨ᵇ f }

-- lemma boolean_realize_sentence_Th (S : bStructure L β) : S ⊨ᵇ Th S :=
-- λf hf, hf

-- lemma is_complete_Th (S : bStructure L β) (HS : nonempty S) : is_complete (Th S) :=
-- ⟨λH, by cases H; apply soundness H HS (boolean_realize_sentence_Th S), λ(f : sentence L), classical.em (S ⊨ᵇ f)⟩

-- def eliminates_quantifiers : Theory L → β :=
--   λ T, ∀ f ∈ T, ∃ f' , bounded_preformula.quantifier_free f' ∧ (T ⊢' f ⇔ f')

-- def L_empty : Language :=
--   ⟨λ _, empty, λ _, empty⟩

-- def T_empty (L : Language) : Theory L := ∅

-- @[reducible] def T_equality : Theory L_empty := T_empty L_empty

-- @[simp] lemma in_theory_iff_satisfied {L : Language} {f : sentence L} : f ∈ Th S = S ⊨ᵇ f :=
--   by refl

-- @[simp] lemma alls_all_commute {L : Language} (f : formula L) {k : ℕ} : (alls k ∀' f) = (∀' alls k f) := by {induction k, refl, dunfold alls, rw[k_ih]}

-- @[simp] lemma alls_succ_k {L : Language} (f : formula L) {k : ℕ} : alls (k + 1) f = ∀' alls k f := by constructor
