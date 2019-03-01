import fol set_theory.zfc set_theory.ordinal order.boolean_algebra order.complete_boolean_algebra .to_mathlib

open lattice
universes u v
variables {β : Type u} [complete_boolean_algebra β]

@[reducible, simp]def inf_context : list β → β
| [] := ⊤
| (x::xs) := x ⊓ (inf_context xs)

@[reducible]def bv_provable (l : list β) (b : β) : Prop :=
  inf_context l ≤ b

infix ` ⊢ᴮ `:50 := bv_provable

lemma bv_prf {a b : β} {l : list β} {h_l : inf_context l = a} {h_p : l ⊢ᴮ b} : a ≤ b := 
by finish

-- TODO(jesse): write a tactic so that l can be replaced by an auto_param
-- which generates the list by folding over the goal

-- also should probably make this into a custom tactic state

@[simp]lemma eq_top_of_empty_context {b : β} : bv_provable list.nil b ↔ b = ⊤ :=
by split; finish[bv_provable]

lemma inf_context_append {l₁ l₂ : list β} : inf_context (l₁ ++ l₂) = inf_context l₁ ⊓ inf_context l₂ := sorry

lemma swap_head : ∀ {c₁ c₂ : β} {l : list β} , inf_context (c₁::c₂::l) = inf_context(c₂::c₁::l)
| c₁ c₂ [] := by simp[inf_comm]
| c₁ c₂ (x::xs) :=
begin
  change inf_context ([c₁, c₂, x] ++ xs) = inf_context ([c₂, c₁, x] ++ xs),
  simp only [inf_context_append], congr' 1, simp, ac_refl
end

lemma weakening' {l : list β} {c : β} : inf_context (c::l) ≤ inf_context l :=
by {induction l, simp, unfold inf_context, apply inf_le_right}

lemma bv_trans_left {l₁ l₂ b} {h₁ : bv_provable l₂ (b : β)} {h₂ : inf_context l₁ ≤ inf_context l₂} : bv_provable l₁ b :=
le_trans h₂ h₁

lemma bv_weakening {l : list β} {c : β} {b : β} : bv_provable l b → bv_provable (c::l) b :=
by {intro H, have := @weakening' _ _ l c, apply bv_trans_left, tidy}

lemma bv_cases_head {l : list β} {c₁ c₂ : β} {b : β} : bv_provable (c₁ :: c₂ :: l) b → bv_provable (c₁ ⊓ c₂ :: l) b :=
by {intro H, apply bv_trans_left, exact H, finish}

lemma bv_prf_and_intro {l : list β} {b₁ b₂ : β} : bv_provable l (b₁) ∧ bv_provable l (b₂) → bv_provable l (b₁ ⊓ b₂) :=
by {intro H, cases H, apply le_inf, tidy}

lemma bv_weakening' {l₁ l₂ : list β} {h_sub : l₁ ⊆ l₂} {b : β} : bv_provable l₁ b → bv_provable l₂ b := sorry

lemma bv_axm {b : β} : [b] ⊢ᴮ b := by simp[bv_provable]

lemma bv_exact {l : list β} (c : β) (h_c : c ∈ l) {b : β} (h' : c = b . tactic.interactive.refl) : l ⊢ᴮ b :=
by {repeat{cases h'}, fapply bv_weakening', exact [c], finish, apply bv_axm}

example : [⊤] ⊢ᴮ (⊤ : β) :=
begin
  apply bv_exact, simp
end



-- include β 
-- example : true :=
-- begin
--   let this : β := ⊥,
--   let hewwo := inf_context ([this, this]),
--   have : hewwo = ⊤ ⊓ ⊥ ⊓ ⊥, by {dsimp[hewwo], unfold inf_context, unfold list.foldl, }
-- end
