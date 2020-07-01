/-
Copyright (c) 2020 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Jesse Michael Han

Showing that Set is formally a model of ZFC.
-/

import .zfc
import .pSet_ordinal
import tactic
import .fol

open fol
local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`:0) := l

def Set_structure_fun_map : Π {n : ℕ}, L_ZFC.functions n → dvector Set n → Set := λ n f,
begin
  cases f,
    { exact λ _, Set.empty },
    { intro z, cases z, refine Set.pair z_x _, cases z_xs, exact z_xs_x },
    { exact λ _, Set.omega },
    { intro z, cases z, exact Set.powerset z_x },
    { intro z, cases z, exact Set.Union z_x }
end

def Set_structure_rel_map : Π {n : ℕ}, L_ZFC.relations n → dvector Set n → Prop := λ n f,
begin
  cases f, intro z, cases z, refine Set.mem z_x _, cases z_xs, exact z_xs_x
end

def Set_structure : Structure L_ZFC :=
 { carrier := Set,
   fun_map := λ n f, Set_structure_fun_map f,
   rel_map := λ n R, Set_structure_rel_map R }

local infix ` ∈'`:100 := _root_.mem
local infix ` ∈ᴾ`:100 := Set.mem

@[simp]
lemma realize_bounded_formula_mem {n} {v : dvector Set_structure n} (t₁ t₂ : bounded_term L_ZFC n) :
  realize_bounded_formula v (t₁ ∈' t₂) ([]) =
  realize_bounded_term v t₁ ([]) ∈ᴾ realize_bounded_term v t₂ ([]) := rfl

lemma Set_models_extensionality : Set_structure ⊨ axiom_of_extensionality :=
begin
  simp[ssatisfied, axiom_of_extensionality], exact λ _ _ H_ext, Set.ext H_ext
end

theorem Set_ZFC : Set_structure ⊨ ZFC :=
begin
  intros ϕ Hϕ, repeat {auto_cases}; try {subst Hϕ},
    { sorry },
    { sorry },
    { sorry },
    { sorry },
    { sorry },
    { exact Set_models_extensionality },
    { sorry },
    { sorry },
    { sorry }
end
