/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
import .to_mathlib

/- The proper generality to do this is with directed categories as the indexing objects -/

/- We'll settle for directed types instead -/

--local attribute [instance, priority 0] classical.prop_decidable

universes u v w

namespace colimit

-- def directed {ι : Sort v} (f : ι → α) := ∀x y, ∃z, f x ≼ f z ∧ f y ≼ f z

structure directed_type : Type (u+1) :=
  (carrier : Type u) (rel : carrier → carrier → Prop)
  (h_reflexive : reflexive rel)
  (h_transitive : transitive rel)
  (h_directed : ∀ x y, ∃ z : carrier, rel x z ∧ rel y z)

lemma trans {D : directed_type} {i j k : D.carrier} (h1 : D.rel i j) (h2 : D.rel j k) : D.rel i k
:= begin fapply directed_type.h_transitive, exact j, repeat{assumption} end

structure directed_diagram (D : (directed_type : Type (u+1))) : Type (max (u+1) (v+1)) :=
  (obj : D.carrier → Type v)
  (mor : ∀{x}, ∀{y}, D.rel x y → (obj x  → obj y))
  (h_mor : ∀{x} {y} {z} {f1 : D.rel x y} {f2 : D.rel y z} {f3 : D.rel x z},
           (mor f3) = (mor f2) ∘ (mor f1)) -- functoriality

@[reducible]def directed_type_of_nat : directed_type :=
  begin refine ⟨ℕ, (≤), _, _, _⟩, intro, refl,
  fapply le_trans, intros, fapply exists.intro, exact x + y,
  simp only [*, zero_le, le_add_iff_nonneg_right, and_self, le_add_iff_nonneg_left]
  end

notation `ℕ'` :=  directed_type_of_nat

@[simp]lemma ℕ_of_ℕ'.carrier : (ℕ').carrier = ℕ := by refl
@[simp]lemma le_of_ℕ'.rel : (ℕ').rel = nat.le := by refl

-- @[reducible]def has_le_ℕ' : has_le (ℕ').carrier := begin split, rw[ℕ_of_ℕ'.carrier], exact λ x y, x ≤ y end
-- attribute [instance] has_le_ℕ'

def constant_functor (D : directed_type) (A : Type v) : directed_diagram D :=
  ⟨(λ x, A), λ x y h, id, by simp⟩

def coproduct_of_directed_diagram {D : (directed_type : Type (u+1)) }
    (F : (directed_diagram D :  Type (max (u+1) (v+1)))) :  Type (max u v) :=
    Σ a : D.carrier, F.obj a

def canonical_inclusion_coproduct {D : directed_type} {F : directed_diagram D} (i : D.carrier) :
                                  F.obj i → coproduct_of_directed_diagram F := λ x, ⟨i,x⟩

def germ_relation {D : (directed_type : Type (u+1)) }
(F : (directed_diagram D :  Type (max (u+1) (v+1)))) : coproduct_of_directed_diagram F → coproduct_of_directed_diagram F  → Prop :=
λ ⟨i,x⟩ ⟨j, y⟩, ∃ k : D.carrier, ∃ z : F.obj k, ∃ f_x : D.rel i k, ∃ f_y : D.rel j k,
                 (F.mor f_x) x = z ∧ (F.mor f_y) y = z

lemma germ_equivalence {D : (directed_type : Type (u+1)) }
(F : (directed_diagram D :  Type (max (u+1) (v+1)))) : equivalence (germ_relation F) :=
begin
  split,
    {rintro ⟨i, x⟩, repeat{split}, swap, exact i, exact D.h_reflexive i},
  split,
    {intros x y, rcases x with ⟨i, x⟩, rcases y with ⟨j, y⟩, intro h,
    rcases h with ⟨ℓ,z,f_x,f_y,H⟩, repeat{fapply exists.intro},
    exacts [ℓ,z,f_y,f_x, and.intro H.right H.left]},
    {unfold transitive, intros x y z a a_1,
    cases x with i x, cases y with j y, cases z with k z,
    rcases a with ⟨ℓ₁, z, fi, fj_1, Hℓ₁⟩, rcases a_1 with ⟨ℓ₂, z', fj_2, fk, Hℓ₂⟩,
    have a_2 := D.h_directed ℓ₁ ℓ₂, rcases a_2 with ⟨ℓ₃, g1, g2⟩,
    have f1 : D.rel i (ℓ₃),
      {fapply D.h_transitive, exacts [ℓ₁, fi, g1]},
    have f2 : D.rel j ℓ₃,
      {fapply D.h_transitive, exacts [ℓ₁, fj_1, g1]},
    have f3 : D.rel k (ℓ₃),
      {fapply D.h_transitive, exacts [ℓ₂, fk, g2]},
    have H1 : F.mor f1 = F.mor g1 ∘ F.mor fi; have H2_l : F.mor f2 = F.mor g1 ∘ F.mor fj_1;
    have H2_r : F.mor f2 = F.mor g2 ∘ F.mor fj_2; have H3 : F.mor f3 = F.mor g2 ∘ F.mor fk;
    all_goals{try{fapply F.h_mor}},
    have H4 : (F.mor fi x) = (F.mor fj_1 y), by cc, dedup,
    have H5 : (F.mor fk z) = (F.mor fj_2 y), by cc,
    unfold germ_relation at *, fapply exists.intro,
    exact ℓ₃, fapply exists.intro, exact (F.mor f2) y, fapply exists.intro, exact f1,
    fapply exists.intro, exact f3, fapply and.intro,
    {simp[H1, H2_l], rw[H4]}, {simp[H2_r, H3], rw[H5]},
    }
end


@[reducible]def coproduct_setoid {D : directed_type} (F : directed_diagram D) : setoid $ coproduct_of_directed_diagram F := ⟨germ_relation F, germ_equivalence F⟩
attribute [instance] coproduct_setoid

def colimit {D : (directed_type : Type (u+1)) } (F : (directed_diagram D :  Type (max (u+1) (v+1)))) : Type (max u v) :=
  @quotient (coproduct_of_directed_diagram F) (by fapply coproduct_setoid)

def canonical_map {D : directed_type} {F : directed_diagram D} (i : D.carrier) :
                  F.obj i → colimit F := (by apply quotient.mk) ∘ canonical_inclusion_coproduct i

lemma canonical_map_inj_of_transition_maps_inj {D : directed_type} {F : directed_diagram D} (i : D.carrier) (H : ∀ {i} {j}, ∀ h : D.rel i j, function.injective (F.mor h)) : function.injective (@canonical_map D F i) :=
begin
    unfold function.injective canonical_map canonical_inclusion_coproduct, intros x y,
    simp only [function.comp_app, quotient.eq], simp only [(≈)],
    unfold germ_relation, intro H_eqv, rcases H_eqv with ⟨j,z,edge,_, ⟨H1, H2⟩⟩,
    exact H edge (by cc)
end

structure cocone {D} (F : directed_diagram D) :=
  (vertex : Type*)
  (map : Π i : D.carrier, F.obj i → vertex)
  (h_compat : ∀{i}, ∀{j}, Π h : D.rel i j, (map i) = (map j) ∘ (F.mor h))

def cocone_of_colimit {D} (F : directed_diagram D) : cocone F :=
  begin
  refine ⟨colimit F, canonical_map, _⟩, intros i j H, fapply funext, intro x,
  simp only [quotient.eq,(≈),canonical_map,function.comp], have h_refl : D.rel j j,
  by apply D.h_reflexive, refine ⟨j,F.mor H x, H, h_refl, rfl, _⟩,
  change ((F.mor h_refl) ∘ (F.mor H)) x = F.mor H x, rw[<-F.h_mor]
end

/- Given a cocone V over a diagram D, return the canonical map colim D → V-/
def universal_map {D} {F : directed_diagram D} {V : cocone F} : colimit F → (V.vertex) :=
begin
  fapply quotient.lift, {exact λp, V.map p.fst p.snd},
  { intros p q H, rcases p with ⟨i,x⟩, rcases q with ⟨j,y⟩,
    simp only [(≈), germ_relation] at H,
    obtain ⟨k , z , f1 , f2, ⟨H1 , H2⟩⟩ := H,
    change V.map i x = V.map j y,
    have : V.map i x = V.map k (F.mor f1 x),
    simp only [V.h_compat f1, eq_self_iff_true, function.comp_app],
    have : V.map j y = V.map k (F.mor f2 y),
    simp only [V.h_compat f2, eq_self_iff_true, function.comp_app],
    simp only [*, eq_self_iff_true],
  }
end

@[simp]lemma universal_map_property {D} {F : directed_diagram D} {V : cocone F} (i : D.carrier) (x) : universal_map ((canonical_map i) x) = (V.map i) x := by refl

/- this generalizes canonical_map_inj_of_transition_maps_inj, because every colimit
   is a cocone over its own diagram

   If the maps to the vertex are injective, then the comparison map from the colimit
   is injective.
-/

lemma universal_map_inj_of_components_inj {D} {F : directed_diagram D} {V : cocone F} (h_inj : ∀ i : D.carrier, function.injective (V.map i)) : function.injective (universal_map : colimit F → (V.vertex)) :=
begin
unfold universal_map, rintros ⟨i,x⟩ ⟨j,y⟩ H, unfold quotient.lift at H, dsimp[colimit] at *, change (⟦⟨i,x⟩⟧ : colimit F) = (⟦⟨j,y⟩⟧ : colimit F),
simp[quotient.eq, (≈)], have := (D.h_directed i j), rcases this with ⟨k, Hik, Hjk⟩,
refine ⟨k, F.mor Hik x, Hik, Hjk, rfl, _⟩, fapply h_inj k,
simp only [*, V.h_compat Hik, V.h_compat Hjk, function.injective.eq_iff, eq_self_iff_true, function.comp_app] at *
end

/- Given a germ-equivalence class from the colimit, return a representative from the coproduct and a proof that this is a lift  -/
noncomputable def germ_rep {D} {F : directed_diagram D} (a : colimit F) :
  Σ' x : (coproduct_of_directed_diagram F), ⟦x⟧ = a :=
classical.psigma_of_exists (quotient.exists_rep a)

@[simp]lemma canonical_map_quotient {D} {F : directed_diagram D} (a : coproduct_of_directed_diagram F) : canonical_map a.fst a.snd = ⟦a⟧ :=
by {cases a, refl}

/- Assuming canonical maps into the colimit are injective, ⟨i,x⟩ and ⟨j,y⟩ in the same fiber
over a ⟦z⟧ : colimit F are related by any transition map i → j. -/
@[simp]lemma eq_mor_of_same_fiber {D} {F : directed_diagram D}
  (a b : coproduct_of_directed_diagram F) {z : colimit F}
  (Ha : ⟦a⟧ = z) (Hb : ⟦b⟧ = z)
  (H_inj : ∀ i : D.carrier, function.injective (@canonical_map D F i))
  (H_rel : D.rel a.fst b.fst) : F.mor H_rel a.snd = b.snd :=
begin
have H_eq : z = canonical_map (b.fst) (F.mor H_rel (a.snd)), by
  {have := (cocone_of_colimit F).h_compat, have H := congr_fun (@this a.fst b.fst H_rel) a.snd,
  dsimp[cocone_of_colimit] at H, rw[canonical_map_quotient, Ha] at H, exact H},
have : canonical_map (b.fst) (b.snd) = canonical_map (b.fst) (F.mor H_rel (a.snd)),
simp only [*, canonical_map_quotient b, colimit.canonical_map_quotient, function.injective.eq_iff, eq_self_iff_true],
fapply H_inj b.fst, symmetry, exact this
end

@[simp]lemma eq_mor_of_same_fiber' {D} {F : directed_diagram D} (a_fst b_fst : D.carrier) (a_snd : F.obj a_fst) (b_snd : F.obj b_fst) {z : colimit F} (Ha : ⟦(⟨a_fst, a_snd⟩ : coproduct_of_directed_diagram F)⟧ = z) (Hb : ⟦(⟨b_fst, b_snd⟩ : coproduct_of_directed_diagram F)⟧ = z) (H_inj : ∀ i : D.carrier, function.injective (@canonical_map D F i)) (H_rel : D.rel a_fst b_fst) : F.mor H_rel a_snd = b_snd :=
begin
  let a : coproduct_of_directed_diagram F := ⟨a_fst, a_snd⟩,
  let b : coproduct_of_directed_diagram F := ⟨b_fst, b_snd⟩,
  have : ⟦a⟧ = z, by assumption, have : ⟦b⟧ = z, by assumption,
  change F.mor H_rel a.snd = b.snd, have := @eq_mor_of_same_fiber D F a b z _ _ _ _,
  repeat{assumption},
end

/- Given an x : F_i and a j : ℕ, apply the map to obtain x' : F_{i+j} -/
@[reducible]def push_to_sum_r {F : directed_diagram ℕ'} {i} (x : F.obj i) (j) : F.obj (i+j) :=
F.mor (by simp only [zero_le, le_add_iff_nonneg_right]) x

@[reducible]def push_to_sum_l {F : directed_diagram ℕ'} {j} (x : F.obj j) (i) : F.obj (i+j) :=
F.mor (by simp only [zero_le, le_add_iff_nonneg_right, add_comm]) x

/- The push_to of x is in the same germ-equivalence class of x -/
lemma same_fiber_as_push_to_r {F : directed_diagram ℕ'} {i} (x : F.obj i) (j) :
     canonical_map i x = canonical_map (i+j) (push_to_sum_r x j)  :=
begin
  have h := congr_fun (@cocone.h_compat _ _ (cocone_of_colimit F) i (i+j) (nat.le_add_right _ _)) x,
  dsimp only [cocone_of_colimit] at h,
  simp only [push_to_sum_r, h],
end

lemma same_fiber_as_push_to_l {F : directed_diagram ℕ'} {j} (x : F.obj j) (i) :
     canonical_map j x = canonical_map (i+j) (push_to_sum_l x i)  :=
begin
  have h := congr_fun (@cocone.h_compat _ _ (cocone_of_colimit F) j (i+j) (nat.le_add_left _ _)) x,
  dsimp only [cocone_of_colimit] at h,
  simp only [push_to_sum_l, h],
end

end colimit
namespace omega_colimit
open colimit

/- Facts about directed colimits indexed by ℕ'. -/
def diagram.mk.map {F : ℕ → Type*}
  (h_succ : ∀{i : ℕ}, F i → F (i+1)) :
  Π {x y : ℕ}, x ≤ y → F x → F y
| 0     0 h := id -- by {rw[nat.eq_zero_of_le_zero h], exact id}
| (x+1) 0 h := false.elim (nat.not_succ_le_zero _ h)
| 0 (y+1) h := h_succ ∘ (diagram.mk.map (nat.le_of_le_and_ne_succ h (nat.succ_ne_zero y).symm))
| (x+1) (y+1) h := dite (x + 1 = y + 1)
  (λ heq, cast (congr_arg F heq) )
  (λ hneq, h_succ ∘ (diagram.mk.map (nat.le_of_le_and_ne_succ h hneq)))

@[simp]lemma diagram.mk.map_self_id {F : ℕ → Type*} {h_succ : ∀(i : ℕ), F i → F (i+1)} (x : ℕ) :
                  @diagram.mk.map F @h_succ x x (by constructor) = id :=
by {induction x, tidy, simp[diagram.mk.map,*]}

lemma diagram.mk.map_le_succ {F : ℕ → Type*} {h_succ : ∀{i : ℕ}, F i → F (i+1)} :
  Π {x y : ℕ} (h : x ≤ y+1) (hneq : x ≠ y + 1),
  @diagram.mk.map _ (λ i, @h_succ i) _ _ h  =
  h_succ ∘ (@diagram.mk.map _ (λ i, @h_succ i) _ _
    (nat.le_of_le_and_ne_succ h hneq))
| 0     y h hneq := rfl
| (x+1) y h hneq := by simp only [diagram.mk.map, dif_neg hneq]

/- If the successive maps of h_succ are injective, then all their compositions are injective -/
lemma diagram.mk.map_inj
  {F : ℕ → Type*} {h_succ : ∀(i : ℕ), F i → F (i+1)}
  {h_inj : ∀ {i : ℕ}, function.injective (@h_succ i )} :
  Π {x y : ℕ} (h : x ≤ y), function.injective (@diagram.mk.map F h_succ x y h)
| 0     0 h := function.injective_id
| (x+1) 0 h := (nat.not_succ_le_zero _ h).elim
| 0 (y+1) h := function.injective.comp h_inj (diagram.mk.map_inj _)
| (x+1) (y+1) h :=
begin
  rw [diagram.mk.map],
  by_cases h' : x + 1 = y + 1,
  {
    simp only [h', dif_pos],
    exact λ _ _, (cast_inj _).mp,
  },
  {
    simp only [h', dif_neg, not_false_iff],
    apply function.injective.comp h_inj,
    apply diagram.mk.map_inj,
  }
end

-- /- Given a ℕ-indexed family of types and a way of assigning maps between successive objects
--    in this family, return the induced directed_diagram over ℕ'. -/
def diagram.mk (F : ℕ → Type*) (h_succ :∀{i : ℕ}, F i → F (i+1)) :
  directed_diagram ℕ' :=
⟨F, by {apply diagram.mk.map, assumption}, λ x y z Hxy Hyz Hxz,
begin
  induction z with z hz,
  {
    induction y with y hy, induction x with x hx,
    {dsimp[diagram.mk.map], refl},
    {by {exfalso, fapply nat.succ_ne_zero, exact x, apply (nat.le_zero_iff).mp, assumption}},
    {by {exfalso, fapply nat.succ_ne_zero, exact y, apply (nat.le_zero_iff).mp, assumption}},
  },
  {
    by_cases hyz : y = z+1,
    subst hyz; by_cases x = z+1; {repeat{dsimp[diagram.mk.map], simp*, refl}},
    by_cases hxz : x = z+1,
    {exfalso, have h'': y < z+1 := lt_of_le_of_ne Hyz hyz, dsimp at *, linarith},
    {
      have h_x : x ≤ z; have h_y : y ≤ z,
      all_goals{try{apply nat.le_of_le_and_ne_succ, repeat{assumption}}},
      dsimp[diagram.mk.map],
      rw diagram.mk.map_le_succ Hxz hxz,
      rw diagram.mk.map_le_succ Hyz hyz,
      simp only [nat.le_of_le_and_ne_succ, @hz h_y h_x],
    }
  }
end
⟩

-- TODO refactor henkin_language_chain et al in terms of diagram.mk

end omega_colimit
