import .bvm_extras .collapse tactic.elide

/-
  Forcing the continuum hypothesis.
-/

universe u

open lattice bSet topological_space pSet cardinal

local infix ` ⟹ `:65 := lattice.imp

local infix ` ⇔ `:50 := lattice.biimp

local infix `≺`:70 := (λ x y, -(larger_than x y))

local infix `≼`:70 := (λ x y, injects_into x y)

@[reducible]private noncomputable definition ℵ₁ : pSet.{u} := (card_ex $ aleph 1)

local notation `ω` := (bSet.omega)

local attribute [instance, priority 0] classical.prop_decidable

section lemmas

variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

/-- Corresponds to proposition 5.2 in Moore's 'the method of forcing':
Let x be a set and let ϕ(v) be a formula in the forcing language. If ∀ y ∈ x, p ⊩ ϕ(y̌), then p ⊩ ∀ y ∈ (x̌), ϕ(y)
-/
lemma check_forall (x : pSet.{u}) (ϕ : bSet 𝔹 → 𝔹) {h : B_ext ϕ} {b : 𝔹} :
  (∀ (y : x.type), b ≤ ϕ((x.func y)̌ )) → (b ≤ (⨅(y : x.type), ϕ((x.func y)̌ ))) :=
λ H, le_infi ‹_›

lemma aleph_one_check_is_aleph_one_of_omega_lt {Γ : 𝔹} (H : Γ ≤ bSet.omega ≺ (ℵ₁)̌ ): Γ ≤ (ℵ₁̌ ) =ᴮ (aleph_one) :=
begin
  refine subset_ext aleph_one_check_sub_aleph_one _,
  have := @aleph_one_satisfies_Ord_spec _ _ Γ, unfold aleph_one_Ord_spec at this,
  bv_split, bv_split_at this_left,
  refine this_right (ℵ₁ ̌) (by simp) _, dsimp at H, rw ←imp_bot at ⊢ H,
  bv_imp_intro H', exact H (larger_than_of_surjects_onto $ surjects_onto_of_injects_into ‹_›)
end

theorem CH_true_aux
  (H_aleph_one : ∀{Γ : 𝔹}, Γ ≤ aleph_one_weak_universal_property (ℵ₁̌ ))
  (H_not_lt    : ∀{Γ : 𝔹}, Γ ≤ - ((ℵ₁)̌  ≺ 𝒫(ω)))
  : ∀{Γ : 𝔹}, Γ ≤ CH :=
begin
  intro Γ, unfold CH, rw[<-imp_bot], bv_imp_intro,
  bv_cases_at H x, bv_cases_at H_1 y, clear H H_1, bv_split, bv_split,
  unfold aleph_one_weak_universal_property at H_aleph_one,
  replace H_aleph_one := @H_aleph_one Γ_3 x ‹_›,
  suffices H_aleph_one_lt_continuum : Γ_3 ≤ (ℵ₁)̌  ≺ 𝒫(ω),
    from bv_absurd _ H_aleph_one_lt_continuum H_not_lt,
  from bSet_lt_of_lt_of_le _ y _ (bSet_lt_of_le_of_lt _ x _ ‹_› ‹_›) ‹_›
end

-- note: CH₂ assumes that ℵ₁̌  ≼ ℵ₁, but this is always true for general 𝔹 (see 1.42ii in Bell)
noncomputable def CH₂ : 𝔹 := (-(ℵ₁̌  ≺ 𝒫(ω))) ⊓ (ω ≺ ℵ₁̌ )

def rel_of_array
  (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
  : bSet 𝔹 :=
set_of_indicator (λ pr, (af pr.1 pr.2) : (prod x y).type → 𝔹)

lemma rel_of_array_surj (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
  (H_bval₁ : ∀ i, x.bval i = ⊤)
  (H_bval₂ : ∀ i, y.bval i = ⊤)
  (H_wide : ∀ j, (⨆ i, af i j) = ⊤) {Γ}
  : Γ ≤ (is_surj x y (rel_of_array x y af)) :=
begin
  bv_intro z, bv_imp_intro Hz, rw[<-@bounded_exists 𝔹 _ x _ _],
  simp [H_bval₁],
    { rw[bSet.mem_unfold] at Hz, bv_cases_at Hz i, simp[H_bval₂] at Hz_1,
     apply bv_rw' Hz_1,
       { apply B_ext_supr, intro i,
       from @B_ext_pair_right 𝔹 _ (λ z, z ∈ᴮ rel_of_array x y af) (by simp) _},
       { rw[rel_of_array], simp, rw[supr_comm],
         transitivity ⨆ (j : type x), af j i ⊓
           pair (func x j) (func y i) =ᴮ pair (func x j) (func y i),
        conv {congr, skip, congr, funext, rw[bv_eq_refl _]}, simp[H_wide],
        clear_except, tidy_context,
        bv_cases_at a j, refine bv_use (j,i),
        refine bv_use j, from ‹_›}},
    { change B_ext _, from B_ext_term _ _ (B_ext_mem_left) (by simp) }
end

lemma mem_left_of_mem_rel_of_array {x y w₁ w₂ : bSet 𝔹} {af : x.type → y.type → 𝔹}
  {Γ} (H_mem_left : Γ ≤ pair w₁ w₂ ∈ᴮ rel_of_array x y af)
  (H_bval₁ : ∀ i, x.bval i = ⊤)
  : Γ ≤ w₁ ∈ᴮ x :=
begin
  unfold rel_of_array at H_mem_left, dsimp at H_mem_left,
  bv_cases_at H_mem_left p, cases p with i j, dsimp at H_mem_left_1,
  bv_split_at H_mem_left_1, have := eq_of_eq_pair_left' ‹_›,
  apply bv_rw' this, simp, from mem.mk'' (by simp only [H_bval₁ _, le_top])
end

lemma mem_right_of_mem_rel_of_array {x y w₁ w₂ : bSet 𝔹} {af : x.type → y.type → 𝔹}
  {Γ} (H_mem_right : Γ ≤ pair w₁ w₂ ∈ᴮ rel_of_array x y af)
  (H_bval₂ : ∀ i, y.bval i = ⊤)
  : Γ ≤ w₂ ∈ᴮ y :=
begin
  unfold rel_of_array at H_mem_right, dsimp at H_mem_right,
  bv_cases_at H_mem_right p, cases p with i j, dsimp at H_mem_right_1,
  bv_split_at H_mem_right_1, have := eq_of_eq_pair_right' ‹_›,
  apply bv_rw' this, simp, apply mem.mk'', simp only [H_bval₂ _, le_top]
end

local attribute [instance] classical.prop_decidable

lemma rel_of_array_extensional (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
  (H_bval₁ : ∀ i, x.bval i = ⊤)
  (H_bval₂ : ∀ i, y.bval i = ⊤)
  (H_wide : ∀ j, (⨆ i, af i j) = ⊤) -- TODO(floris): remove this
  (H_anti : ∀ i, (∀ j₁ j₂, j₁ ≠ j₂ → af i j₁ ⊓ af i j₂ ≤ ⊥))
  (H_inj  : ∀ i₁ i₂, ⊥ < (func x i₁) =ᴮ (func x i₂) → i₁ = i₂) -- can probably be removed also
  {Γ}
  : Γ ≤ (is_func (rel_of_array x y af)) :=
begin
  bv_intro w₁, bv_intro v₁, bv_intro w₂, bv_intro v₂,
  bv_imp_intro H_mem, bv_split,
  bv_imp_intro H_eq,
  have this : Γ_2 ≤ pair w₁ v₂ ∈ᴮ rel_of_array x y af,
    by {apply bv_rw' H_eq,
          { exact B_ext_term _ _ (B_ext_mem_left) (by simp) },
          { from ‹_› }},
  clear_except H_mem_left this H_anti H_inj H_eq,
  dsimp[rel_of_array] at H_mem_left this,
  bv_cases_at H_mem_left p₁, cases p₁ with i₁ j₁,
  suffices : Γ_3 ≤ v₂ =ᴮ (y.func j₁),
    by {refine bv_trans _ (bv_symm this), bv_split,
         from eq_of_eq_pair_right' ‹_›},
  bv_cases_at this p₂, cases p₂ with i₂ j₂,
  suffices : Γ_4 ≤ (y.func j₂) =ᴮ (func y j₁),
    by {exact bv_trans (by bv_split; from eq_of_eq_pair_right' ‹_›) (this)},
  by_cases j₁ = j₂,
    { subst h, from bv_refl},
    { bv_exfalso, by_cases i₁ = i₂,
        { subst h, specialize H_anti i₁ j₁ j₂ ‹_›, refine le_trans _ H_anti,
          bv_split, bv_split_goal},
        { suffices : Γ_4 ≤ - (w₁ =ᴮ v₁),
            by {exact bv_absurd (w₁ =ᴮ v₁) ‹_› ‹_›},
          suffices : Γ_4 ≤ w₁ =ᴮ (func x i₁) ∧ Γ_4 ≤ v₁ =ᴮ (func x i₂),
            by { clear_except H_inj this h,
                 apply bv_rw' this.left, by simp,
                 apply bv_rw' this.right, by simp,
                 suffices H_le_bot : (func x i₁ =ᴮ func x i₂) ≤ ⊥,
                   by {rw[<-imp_bot, <-deduction], from le_trans (by simp) H_le_bot},
                 suffices H_not_bot_lt : ¬ (⊥ < func x i₁ =ᴮ func x i₂),
                   by {clear_except H_not_bot_lt, finish[bot_lt_iff_not_le_bot]},
                 clear_except H_inj h, intro H, from absurd (H_inj _ _ H) ‹_›},
          bv_split,
          exact ⟨eq_of_eq_pair_left' H_mem_left_1_right,
                   bv_trans (bv_symm H_eq) (eq_of_eq_pair_left' this_1_right)⟩}}
end

lemma rel_of_array_is_func'  (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
  (H_bval₁ : ∀ i, x.bval i = ⊤)
  (H_bval₂ : ∀ i, y.bval i = ⊤)
  (H_wide : ∀ j, (⨆ i, af i j) = ⊤)
  (H_tall : ∀ i, (⨆ j, af i j) = ⊤) -- this is not in the book, but I think it should be
  (H_anti : ∀ i, (∀ j₁ j₂, j₁ ≠ j₂ → af i j₁ ⊓ af i j₂ ≤ ⊥))
  (H_inj  : ∀ i₁ i₂, ⊥ < (func x i₁) =ᴮ (func x i₂) → i₁ = i₂)
  {Γ}
  : Γ ≤ is_func' x y (rel_of_array x y af) :=
begin
  refine le_inf (by apply rel_of_array_extensional; assumption) _, rw bSet.is_total,
  rw[<-bounded_forall], bv_intro i_x, bv_imp_intro Hi_x, rw[<-bounded_exists],
    { simp[*,rel_of_array, -Γ_1], rw[supr_comm, supr_prod],
      apply bv_use i_x,
      transitivity ⨆ (j : type y),
      af ((i_x, j).fst) ((i_x, j).snd) ⊓ pair (func x i_x) (func y j) =ᴮ pair (func x ((i_x, j).fst)) (func y ((i_x, j).snd)),
        { conv { to_rhs, funext, congr, funext,rw[bv_eq_refl] }, simp[H_tall]},
        { exact diagonal_supr_le_supr (by refl) }},
    { change B_ext _, from B_ext_term _ _ (B_ext_mem_left) (by simp) },
    { change B_ext _, apply B_ext_supr, intro, apply B_ext_inf,
      { simp },
      { from B_ext_term _ _ (B_ext_mem_left) (by simp) }}
end

-- any ω-indexed downward chain has a nonzero intersection
def omega_closed (α : Type*) [nontrivial_complete_boolean_algebra α] : Prop :=
∀ (s : ℕ → α) (H_nonzero : ∀ n, ⊥ < s n) (H_chain : ∀ n, s (n+1) ≤ s n), ⊥ < ⨅n, s n

section
local attribute [instance, priority 10] regular_open_algebra
lemma ne_empty_of_subset {α} {s t : set α} (h : s ⊆ t) (hs : s ≠ ∅) : t ≠ ∅ :=
by { rw [set.ne_empty_iff_exists_mem] at hs ⊢, cases hs with x hx, exact ⟨x, h hx⟩ }

lemma omega_closed_regular_opens {α : Type*} [topological_space α] [hα : nonempty α]
  (B : set (set α)) (hB : is_topological_basis B)
  (h : ∀(s : ℕ → B) (H_nonzero : ∀ n, (s n).1 ≠ ∅) (H_chain : ∀ n, s (n+1) ≤ s n),
  ∃t ∈ B, (t : set α) ≠ ∅ ∧ t ⊆ ⨅ n, (s n).1) :
  omega_closed (regular_opens α) :=
begin
  intros s h1s h2s,
  have : ∃(s' : ℕ → B), ∀ n, (s' n).1 ≠ ∅ ∧ (s' n).1 ⊆ s n ∧ (s' (n+1)).1 ⊆ (s' n).1,
  { sorry
    -- apply @classical.axiom_of_choice _ _ (λ n (sn : B), sn.1 ≠ ∅ ∧ sn.1 ⊆ s n ∧ ),
    -- intro n, specialize h1s n, rw [regular_open.bot_lt] at h1s,
    -- cases h1s with x hx,
    -- have := mem_basis_subset_of_mem_open hB hx (is_open_of_is_regular (s n).2),
    -- rcases this with ⟨s, hsB, hxs, hs⟩,
    -- use ⟨s, hsB⟩, dsimp only, rw [set.ne_empty_iff_exists_mem],
    -- exact ⟨⟨x, hxs⟩, hs⟩
    },
  cases this with s' hs',
  rw [forall_and_distrib, forall_and_distrib] at hs', rcases hs' with ⟨h1s', h2s', h3s'⟩,
  rw [regular_open.bot_lt, ←set.ne_empty_iff_exists_mem],
  rcases h s' h1s' h3s' with ⟨t, h1t, h2t, h3t⟩,
  apply ne_empty_of_subset _ h2t,
  rw [fst_infi],
  refine set.subset.trans (in_p_p_of_open $ is_open_of_is_topological_basis hB h1t) _,
  apply p_p_mono, refine set.subset.trans h3t _,
  show (⨅ (n : ℕ), (s' n).val) ≤ ⨅ (i : ℕ), (s i).val,
  refine infi_le_infi _, exact h2s'
end

end

section function_reflect

variables (H_omega_closed : omega_closed 𝔹) {y : pSet.{u}} {g : bSet 𝔹} {Γ : 𝔹} (H_nonzero : ⊥ < Γ) (H : Γ ≤ is_func' bSet.omega y̌ g)

include y g Γ H_nonzero H

local notation `ae₀` := AE_of_check_func_check pSet.omega y H H_nonzero

local notation `aeₖ` := AE_of_check_func_check pSet.omega y

noncomputable def function_reflect.fB : ℕ → Σ' (j : y.type) (B : 𝔹), (⊥ < B ∧ B ≤ is_func' bSet.omega y̌ g)
| 0 := begin
         use classical.some (ae₀ (ulift.up 0)), use classical.some (classical.some_spec (ae₀ (ulift.up 0))),
         rcases classical.some_spec (classical.some_spec (ae₀ (ulift.up 0))) with ⟨_,_,_,_⟩, from ⟨‹_›,‹_›⟩
       end
| (k+1) := begin
             use classical.some ((aeₖ ((function_reflect.fB) k).2.2.2 ((function_reflect.fB) k).2.2.1 ((ulift.up $ k + 1)))),
             use classical.some (classical.some_spec ((aeₖ ((function_reflect.fB) k).2.2.2 ((function_reflect.fB) k).2.2.1 ((ulift.up $ k + 1))))),
             rcases classical.some_spec (classical.some_spec ((aeₖ ((function_reflect.fB) k).2.2.2 ((function_reflect.fB) k).2.2.1 ((ulift.up $ k + 1))))) with ⟨_,_,_,_⟩,
             from ⟨‹_›,‹_›⟩
           end

@[reducible]noncomputable def function_reflect.B : ℕ → 𝔹 := λ n, (function_reflect.fB H_nonzero H n).2.1

@[reducible]noncomputable def function_reflect.f : ℕ → y.type := λ n, (function_reflect.fB H_nonzero H n).1

lemma function_reflect.B_nonzero (n) : ⊥ < (function_reflect.B H_nonzero H n) :=
(function_reflect.fB H_nonzero H n).2.2.left

lemma function_reflect.B_is_func' (n) : (function_reflect.B H_nonzero H n) ≤ is_func' bSet.omega y̌ g :=
(function_reflect.fB H_nonzero H n).2.2.right

lemma function_reflect.B_unfold {n} : function_reflect.B H_nonzero H (n+1)
  = classical.some ((function_reflect.fB._main._proof_5 H_nonzero H n)) -- yuck
:=  rfl

lemma function_reflect.B_le {n} : (function_reflect.B H_nonzero H (n + 1)) ≤ function_reflect.B H_nonzero H n :=
begin
  rw function_reflect.B_unfold, let p := _, change classical.some p ≤ _,
  rcases classical.some_spec p with ⟨_,_,_,_⟩, convert h_w, clear_except, unfold function_reflect.B, cases n, refl, refl,
end


lemma function_reflect.B_pair {n} : (function_reflect.B H_nonzero H n) ≤ pair (pSet.omega.func (ulift.up n))̌  (y.func $ function_reflect.f H_nonzero H n)̌  ∈ᴮ g :=
begin
  cases n,
    { change classical.some _ ≤ _, let p := _, change classical.some p ≤ _,
      rcases classical.some_spec p with ⟨_,_,_,_⟩, from ‹_› },
    { rw function_reflect.B_unfold, let p := _, change classical.some p ≤ _,
      rcases classical.some_spec p with ⟨_,_,_,_⟩, from ‹_› }
end

variable (H_function : Γ ≤ is_function bSet.omega y̌ g)

lemma function_reflect.B_infty_le_Γ : (⨅ n, (function_reflect.B H_nonzero H n)) ≤ Γ :=
begin
  refine infi_le_of_le 0 _, let p := _, change classical.some p ≤ _,
  rcases classical.some_spec p with ⟨_,_,_,_⟩, from ‹_›
end

-- TODO(jesse): come up with a better name
lemma function_reflect_aux : (⨅n, function_reflect.B H_nonzero H n) ≤ (⨅n, pair (pSet.omega.func (ulift.up n))̌  (y.func $ function_reflect.f H_nonzero H n)̌  ∈ᴮ g) :=
infi_le_infi $ λ _, function_reflect.B_pair _ _

noncomputable def function_reflect.f' : pSet.{u} :=
begin
  refine @pSet.function.mk pSet.omega _ _,
  intro k, cases k with k',
  exact y.func (function_reflect.f H_nonzero H k'),
  intros i j Heqv,
  suffices this : i = j,
    by { subst this },
  from pSet.omega_inj ‹_›
end

lemma function_reflect.f'_is_function : ∀ {Γ : 𝔹}, Γ ≤ is_function (pSet.omega)̌  y̌ (function_reflect.f' H_nonzero H)̌  :=
begin
  refine @check_is_func 𝔹 _ pSet.omega y (function_reflect.f' H_nonzero H) _, apply pSet.function.mk_is_func, intro i, cases i, simp
end

lemma function_reflect_aux₂ : (⨅n, function_reflect.B H_nonzero H n) ≤ (⨅n, (pair (pSet.omega.func (ulift.up n))̌  (y.func $ function_reflect.f H_nonzero H n)̌  ∈ᴮ (function_reflect.f' H_nonzero H)̌  ⇔ (pair (pSet.omega.func (ulift.up n))̌  (y.func $ function_reflect.f H_nonzero H n)̌  ∈ᴮ g))) :=
begin
  refine infi_le_infi (λ n, _), tidy_context, refine ⟨_,_⟩; bv_imp_intro H_mem,
    { refine le_trans a _, apply function_reflect.B_pair },
    { apply @bv_rw' _ _ _ _ _ (bv_symm check_pair) (λ z, z ∈ᴮ  (function_reflect.f' H_nonzero H)̌ ), simp,
      refine check_mem _, convert pSet.function.mk_mem, refl }
end

include H_function

lemma function_reflect.B_infty_le_function : (⨅ n, (function_reflect.B H_nonzero H n)) ≤ is_function ω y̌ g :=
le_trans (by apply function_reflect.B_infty_le_Γ) H_function

lemma function_reflect_aux₃ : (⨅n, function_reflect.B H_nonzero H n) ≤ ⨅ (p : bSet 𝔹), p ∈ᴮ prod omegǎ  y̌  ⟹ (p ∈ᴮ (function_reflect.f' H_nonzero H)̌  ⇔ p ∈ᴮ g) := 
begin
  rw ←bounded_forall, swap, {change B_ext _, simp},
  bv_intro pr, rcases pr with ⟨⟨i⟩, j⟩, simp only [prod_check_bval, top_imp, prod_func],
  have := (function_reflect_aux₂ H_nonzero H) i, bv_split_at this,
  refine le_inf _ _; bv_imp_intro H',
    { have this' : Γ_1 ≤ (pair (func omegǎ  {down := i}) (func y̌  j)) =ᴮ (pair (func omega {down := i})̌  (func y (function_reflect.f H_nonzero H i))̌ ),
        by {rw pair_eq_pair_iff, refine ⟨bv_refl, _⟩,
            refine eq_of_is_func'_of_eq (is_func'_of_is_function _) _ _ _, show _ ≤ is_function bSet.omega y̌ (function_reflect.f' H_nonzero H)̌ ,
            refine check_is_func _, apply pSet.function.mk_is_func, intro n, cases n, simp,
            show _ ≤ _ =ᴮ _, apply bv_refl, from H',
            refine this_right _,
            refine le_trans (inf_le_right) (infi_le_of_le i (by apply function_reflect.B_pair))},  
      apply @bv_rw' _ _ _ _ _ this' (λ z, z ∈ᴮ g), simp,
      have := (inf_le_right : Γ_1 ≤ _),
      exact le_trans this (le_trans
              (by apply function_reflect_aux) (infi_le_of_le i (by refl)))},
    { have this' : Γ_1 ≤ (pair (func omegǎ  {down := i}) (func y̌  j)) =ᴮ (pair (func omega {down := i})̌  (func y (function_reflect.f H_nonzero H i))̌ ),
        by {rw pair_eq_pair_iff, refine ⟨bv_refl, _⟩,
            refine eq_of_is_func'_of_eq (is_func'_of_is_function _) _ _ _, show _ ≤ is_function _ _ _, refine le_trans inf_le_right (function_reflect.B_infty_le_function _ _ H_function),
            show _ ≤ _ =ᴮ _, from (bv_refl : _ ≤ (func omegǎ  {down := i}) =ᴮ _), from H',
        refine le_trans (inf_le_right) (infi_le_of_le i _), apply function_reflect.B_pair },
      apply @bv_rw' _ _ _ _ _ this' (λ z, z ∈ᴮ ((function_reflect.f' H_nonzero H)̌ )), simp,
      apply @bv_rw' _ _ _ _ _ (bv_symm check_pair) (λ z, z ∈ᴮ  (function_reflect.f' H_nonzero H)̌ ), simp,
      refine check_mem _, convert pSet.function.mk_mem, refl}
end
-- begin
--   rw ←bounded_forall, swap, {change B_ext _, simp},
--   bv_intro pr, simp only [prod_check_bval, top_imp],
--   rcases pr with ⟨⟨i⟩, j⟩,
--   refine le_inf _ _; bv_imp_intro H',
--     { sorry },
--     { sorry }
-- end

include H_omega_closed
lemma function_reflect_of_omega_closed : ∃ (f : pSet.{u}) (Γ' : 𝔹) (H_nonzero' : ⊥ < Γ') (H_le' : Γ' ≤ Γ), (Γ' ≤ f̌ =ᴮ g) ∧ is_func omega y f :=
begin
  refine ⟨function_reflect.f' H_nonzero H,_⟩,
    { use (⨅ n, function_reflect.B H_nonzero H n), -- this is Γ'
      refine ⟨_,_,⟨_,_⟩⟩,
        { apply H_omega_closed, apply function_reflect.B_nonzero, apply function_reflect.B_le },
        { refine infi_le_of_le 0 _, let p := _, change classical.some p ≤ _,
          rcases classical.some_spec p with ⟨_,_,_,_⟩, from ‹_› },
        { apply bSet.funext, apply function_reflect.f'_is_function,
          refine le_trans _ H_function, {exact function_reflect.B_infty_le_Γ H_nonzero H},
          apply function_reflect_aux₃, from ‹_› },
          { apply pSet.function.mk_is_func, intro n, cases n, simp }}
end

end function_reflect

end lemmas

namespace collapse_algebra

local prefix `#`:50 := cardinal.mk
local attribute [instance, priority 9001] collapse_space

open collapse_poset

local notation `𝔹` := collapse_algebra ((ℵ₁ : pSet.{u}).type) (powerset omega : pSet).type

-- TODO(floris)
lemma 𝔹_omega_closed : omega_closed 𝔹 := sorry

lemma check_functions_eq_functions (y : pSet.{u})
  {Γ : 𝔹} : Γ ≤ check (functions (pSet.omega) y) =ᴮ functions (bSet.omega) y̌ :=
begin
  refine subset_ext check_functions_subset_functions _,
  rw[subset_unfold'], bv_intro g, bv_imp_intro Hg, rw[mem_unfold'],
  let A := _, change _ ≤ A, let B := _, change _ ≤ B at Hg,
  suffices this : A ⊓ B = B,
    by {refine le_trans _ inf_le_left, from B, rw this, simp* },
  apply Sup_eq_top_of_dense_Union_rel, apply rel_dense_of_dense_in_basis B.1 _ collapse_space_basis_spec,
  intros D HD HD_ne, unfold collapse_space_basis at HD, cases HD with p Hp,
    { clear_except p HD_ne, exfalso, finish },
    rcases Hp with ⟨p,⟨_,Hp⟩⟩, subst Hp, let P : 𝔹 := ⟨principal_open p, is_regular_principal_open p⟩,
    have bot_lt_Γ : (⊥ : 𝔹) < P ⊓ B,
    rw [bot_lt_iff_not_le_bot, le_bot_iff], rwa subtype.ext,
    have := function_reflect_of_omega_closed 𝔹_omega_closed bot_lt_Γ
      (by {dsimp[B], refine inf_le_right_of_le (is_func'_of_is_function
            (by { refine poset_yoneda _, tactic.rotate 2, intros Γ HΓ, rw[bSet.mem_functions_iff] at HΓ, convert HΓ }))}) (by {dsimp [B],
              refine poset_yoneda _, intros Γ HΓ, exact bSet.mem_functions_iff.mp (bv_and.right HΓ) }),
    rcases this with ⟨f, Γ', H_nonzero', H_lt', H_pr', H_func'⟩, apply set.inter_sUnion_ne_empty_of_exists_mem,
    let C := g ∈ᴮ (functions omega y)̌  ⊓ g =ᴮ g,
    use C.val, simp, refine ⟨⟨C.property, _⟩, _⟩, use g,
    suffices this : P ⊓ B ⊓ C ≠ ⊥,
      by {change ¬ _ at this, rwa subtype.ext at this }, rw ←bot_lt_iff_ne_bot,
    suffices this : Γ' ≤ C,
      by {exact lt_of_lt_of_le H_nonzero' (le_inf ‹_› ‹_›)},
    refine le_inf _ (bv_refl), apply bv_rw' (bv_symm H_pr'), simp,
    rw ←pSet.mem_functions_iff at H_func', from check_mem H_func'
end

lemma π_χ_regular (p : type (card_ex (aleph 1)) × (powerset omega).type) : @topological_space.is_regular _ collapse_space {g : type (card_ex (aleph 1)) → type (powerset omega) | g (p.fst) = p.snd} :=
by simp

def π_χ : ((ℵ₁ : pSet.{u}).type × (pSet.powerset omega : pSet.{u}).type) → 𝔹 :=
λ p, ⟨{g | g p.1 = p.2}, π_χ_regular _⟩

private lemma eq₀ : ((ℵ₁)̌  : bSet 𝔹).type = (ℵ₁).type := by simp

private lemma eq₀' : ((powerset omega)̌  : bSet.{u} 𝔹).type = (powerset omega).type := by simp

private lemma eq₁ : (((ℵ₁)̌  : bSet 𝔹).type × ((powerset omega)̌  : bSet 𝔹).type) = (((ℵ₁ : pSet.{u}) .type) × (powerset omega : pSet.{u}).type) := by simp

-- lemma aleph_one_type_uncountable' : (aleph 0) < # ℵ₁.type :=
-- by simp only [succ_le, cardinal.aleph_zero, pSet.omega_lt_aleph_one, pSet.mk_type_mk_eq''']

lemma aleph_one_type_uncountable : cardinal.omega.succ ≤ # ℵ₁.type :=
by simp only [succ_le, pSet.omega_lt_aleph_one, pSet.mk_type_mk_eq''']

@[reducible]def π_af : ((ℵ₁̌  : bSet 𝔹) .type) → ((powerset omega)̌  : bSet 𝔹) .type → 𝔹 :=
λ η S, (⟨{g | g (cast eq₀ η) = (cast eq₀' S)}, by simp⟩ : 𝔹)

lemma π_af_wide :  ∀ (j : ((powerset omega)̌ ).type), (⨆ (i : type (ℵ₁̌ )), π_af i j) = (⊤ : 𝔹) :=
begin
 intro S,
   refine Sup_eq_top_of_dense_Union _,
   apply dense_of_dense_in_basis _ collapse_space_basis_spec _,
   intros B HB HB_ne,
   unfold collapse_space_basis at HB, cases HB with p Hp,
   { contradiction }, cases Hp with p Hp,
   simp at Hp, subst Hp,
   refine set.ne_empty_of_exists_mem _,
   { cases exists_mem_compl_dom_of_unctbl p aleph_one_type_uncountable with η Hη,
     use trivial_extension p.f S, use trivial_extension_mem_principal_open,
     change ∃ x, _, use (π_af (cast eq₀.symm η) S).val,
     refine ⟨_, _⟩, change ∃ x, _, refine ⟨_,_⟩,
     apply π_af (cast eq₀.symm η) S, refine ⟨_,_⟩,
       { exact set.mem_range_self _ },
       { refl },
     { unfold trivial_extension, dsimp,
       suffices this : (cast eq₀ (cast eq₀.symm η) ∉ pfun.dom (p.f)),
         by {simpa*},
       intro, apply Hη, cc } }
end

lemma π_af_tall : ∀ (i : (card_ex $ aleph 1)̌ .type), (⨆(j : (powerset omega)̌ .type), π_af i j) = (⊤ : 𝔹) :=
begin
  intro i, refine Sup_eq_top_of_dense_Union _,
  apply dense_of_dense_in_basis _ collapse_space_basis_spec _,
  intros B HB HB_ne,
  unfold collapse_space_basis at HB, cases HB with p Hp,
    { contradiction },
    { cases Hp with p Hp, simp at Hp, subst Hp, refine set.ne_empty_of_exists_mem _,
      let f := classical.choice (classical.nonempty_of_not_empty _ ‹_›),
      use f, use f.property, refine ⟨_,_⟩,
        { exact {g | g (cast eq₀ i) = f.val (cast eq₀ i)} },
        { refine ⟨⟨_,_⟩,by ext; refl⟩,
          { exact ⟨_, π_χ_regular ((cast eq₀ i), f.val (cast eq₀ i))⟩ },
          { exact ⟨⟨f.val (cast eq₀ i), rfl⟩, rfl⟩ }}}
end

lemma π_af_anti : ∀ (i : type (ℵ₁̌  : bSet 𝔹)) (j₁ j₂ : type ((powerset omega)̌ )),
    j₁ ≠ j₂ → π_af i j₁ ⊓ π_af i j₂ ≤ ⊥ :=
λ _ _ _ _ _ h, by cases h; finish

-- TODO(jesse) refactor the proof of the suffices into a more general lemma
lemma aleph_one_inj : (∀ i₁ i₂, ⊥ < (func (ℵ₁̌  : bSet 𝔹) i₁) =ᴮ (func (ℵ₁̌  : bSet 𝔹) i₂) → i₁ = i₂) :=
begin
  suffices this : ∀ (x y : type (ℵ₁)),
    x ≠ y → ¬equiv (func (ℵ₁) x) (func (ℵ₁) y),
    by {intros i₁ i₂ H, haveI : decidable (i₁ = i₂) := classical.prop_decidable _,
        by_contra,
        have H_cast_eq : (cast eq₀ i₁) ≠ (cast eq₀ i₂),
          by {intro, apply a, cc},
        specialize this (cast eq₀ i₁) (cast eq₀ i₂) ‹_›,
        have this₀ := check_bv_eq_bot_of_not_equiv this,
        suffices this₁ : func (ℵ₁̌ ) i₁ =ᴮ func (ℵ₁̌ ) i₂ = ⊥,
          by {exfalso, rw[eq_bot_iff] at this₀, rw[bot_lt_iff_not_le_bot] at H,
              suffices : func (ℵ₁̌  : bSet 𝔹) i₁ =ᴮ func (ℵ₁ ̌) i₂ ≤ ⊥, by contradiction,
              convert_to (func ℵ₁ (cast eq₀ i₁))̌   =ᴮ (func ℵ₁ (cast eq₀ i₂)) ̌ ≤ ⊥,
              apply check_func, apply check_func, from ‹_›},
        convert this₀; apply check_func},
  exact λ _ _ _, ordinal.mk_inj _ _ _ ‹_›
end

noncomputable def π : bSet 𝔹 :=
rel_of_array (ℵ₁̌  : bSet 𝔹) ((powerset omega)̌ ) π_af

-- noncomputable def π : bSet 𝔹 := @set_of_indicator (𝔹 : Type u) _ (prod (ℵ₁̌ ) ((powerset omega)̌ )) (λ z, π_χ (cast eq₁ z))

lemma π_is_func {Γ} : Γ ≤ is_func π :=
begin
  unfold π, refine rel_of_array_extensional _ _ _ (by simp) (by simp) _ _ _,
  { from π_af_wide },
  { from π_af_anti },
  { from aleph_one_inj },
end

lemma π_is_func' {Γ} : Γ ≤ is_func' (ℵ₁̌  : bSet 𝔹) ((powerset omega)̌ ) π :=
begin
  unfold π, refine rel_of_array_is_func' _ _ _ (by simp) (by simp) _ _ _ _,
    { from π_af_wide },
    { from π_af_tall },
    { from π_af_anti },
    { from aleph_one_inj }
end

lemma π_is_functional {Γ} : Γ ≤ is_functional π := is_functional_of_is_func _ π_is_func

lemma π_is_surj {Γ} : Γ ≤ is_surj (ℵ₁̌ ) ((powerset omega)̌ ) π :=
rel_of_array_surj _ _ _ (by simp) (by simp) (π_af_wide)

lemma π_spec {Γ : 𝔹} : Γ ≤ (is_func π) ⊓ ⨅v, v ∈ᴮ (powerset omega)̌  ⟹ (⨆w, w ∈ᴮ (ℵ₁̌ ) ⊓ pair w v ∈ᴮ π) := le_inf π_is_func π_is_surj

lemma π_spec' {Γ : 𝔹} : Γ ≤ (is_func' ((card_ex $ aleph 1)̌ ) ((powerset omega)̌ ) π) ⊓ is_surj ((card_ex $ aleph 1)̌ ) ((powerset omega)̌ ) π:=  le_inf π_is_func' π_is_surj

-- lemma π_spec' {Γ : 𝔹} : Γ ≤ (is_func π) ⊓ ⨅v, v ∈ᴮ (powerset omega)̌  ⟹ (⨆w, w ∈ᴮ (ℵ₁̌ ) ⊓ pair w v ∈ᴮ π) := sorry
-- le_inf π_is_func' π_is_surj

lemma ℵ₁_larger_than_continuum {Γ : 𝔹} : Γ ≤ larger_than (ℵ₁ ̌) ((powerset omega)̌ ) :=
by { apply bv_use (ℵ₁ ̌), apply bv_use π, rw[inf_assoc], from le_inf subset_self π_spec' }

-- for these two lemmas, need 2.17 (iv) in Bell, which follows from (i) ⟹ (ii)
-- i.e. If 𝔹 has a dense subset P which is ω-closed, then for any η < ℵ₁, and any x,
-- bSet 𝔹 ⊩ Func(η̌, x̌) = Func(η, x)̌ .

/-
Proof sketch:
Let p : P be such that p ⊩ f is a function from η̌ to x̌. Using the ω-closed assumption, find a descending sequence {p_i : P} and a set {y_i ∈ x} such that for each i, pᵢ ⊩ f(i) = y_i.

If q ∈ P satisfies q ≤ pᵢ for all i (i.e. is a witness to the ω-closed assumption),
and g is the function attached to the collection of pairs (i, y_i), show that q ⊩ f = ǧ.
-/

-- lemma distributive {x : pSet.{u}} (H_inj : ∀ i₁ i₂ : x.type, pSet.equiv (x.func i₁) (x.func i₂) → i₁ = i₂) (af : pSet.omega.type → x.type → 𝔹) :
--    ⨅ i : pSet.omega.type, (⨆ j : x.type, af i j) = ⨆(f : pSet.omega.type → x.type), ⨅(i : pSet.omega.type), af i (f i)
--  := sorry

-- lemma pSet.func_eq_of_inj {x : pSet.{u}} (H_inj : ∀ i₁ i₂ : x.type, pSet.equiv (x.func i₁) (x.func i₂) → i₁ = i₂) : sorry := sorry

lemma surjection_reflect {Γ : 𝔹} (H_bot_lt : ⊥ < Γ) (H_surj : Γ ≤ surjects_onto ω ℵ₁̌ )
: ∃ (f : pSet.{u}), is_func omega (ordinal.mk (ord (aleph 1))) f
   ∧ is_surj pSet.omega (card_ex $ aleph 1) f :=
begin
  by_contra H, simp only [not_exists, not_and_distrib] at H,
  suffices this : Γ ≤ ⊥,
    by {rw[bot_lt_iff_not_le_bot] at H_bot_lt, contradiction},
  replace H_surj := exists_surjection_of_surjects_onto H_surj,
  bv_cases_at H_surj f Hf, bv_split_at Hf,
  rw[<-bSet.mem_functions_iff] at Hf_left,
  suffices this : Γ_1 ≤ f ∈ᴮ (pSet.functions pSet.omega (ℵ₁))̌ ,
    by { by_contra H', rw[<-bot_lt_iff_not_le_bot] at H',
         replace this := eq_check_of_mem_check H' _ _ this,
         rcases this with ⟨i_g, Γ', H₁,H₂,H₃⟩,
         apply_at Hf_right le_trans H₂,
         apply_at Hf_left le_trans H₂,
         let g : pSet.{u} := (pSet.functions pSet.omega ℵ₁).func i_g,
         specialize H g, cases H,
           { apply_at H check_not_is_func, show 𝔹, from Γ',
           rw[bSet.mem_functions_iff] at Hf_left,
           tactic.rotate 1, apply_instance,
           refine false_of_bot_lt_and_le_bot H₁ (H _),

           change Γ' ≤ f =ᴮ ǧ at H₃, apply_at H₃ bv_symm,
           apply bv_rw' H₃, simp, from Hf_left },
           { apply_at H check_not_is_surj,  show 𝔹, from Γ',
           tactic.rotate 1, apply_instance,
           refine false_of_bot_lt_and_le_bot H₁ (H _),
           change Γ' ≤ f =ᴮ ǧ at H₃, apply_at H₃ bv_symm,
           apply bv_rw' H₃, simp, from Hf_right}
         },
  have : Γ_1 ≤ _,
    from check_functions_eq_functions ℵ₁,
  bv_cc
end

lemma omega_lt_aleph_one {Γ : 𝔹} : Γ ≤ bSet.omega ≺ (ℵ₁̌ ) :=
begin
  unfold larger_than, rw[<-imp_bot, <-deduction],
  /- `tidy_context` says -/ refine poset_yoneda _, intros Γ_1 a, simp only [le_inf_iff] at *, cases a,
  bv_cases_at a_right S HS, apply lattice.context_Or_elim HS,
  intros f Hf, specialize_context Γ_2,
  simp only [le_inf_iff] at Hf, repeat{auto_cases}, by_contra H,
  replace H := (bot_lt_iff_not_le_bot.mpr H),
  suffices : ∃ f : pSet.{u}, is_func pSet.omega (ordinal.mk (aleph 1).ord) f ∧ pSet.is_surj (pSet.omega) (ordinal.mk (aleph 1).ord) f,
    by {exfalso, from ex_no_surj_omega_aleph_one ‹_›},
  suffices : Γ_3 ≤ surjects_onto ω ℵ₁̌ ,
    by {from surjection_reflect H this},
  refine surjects_onto_of_larger_than_and_exists_mem ‹_› _,
  simp only [show ℵ₁ = card_ex (aleph ↑1), by simp],
  from check_exists_mem card_ex_aleph_exists_mem
end

lemma aleph_one_check_universal_property (Γ : 𝔹) : Γ ≤ aleph_one_weak_universal_property (ℵ₁̌  : bSet 𝔹) :=
begin
  apply bv_rw' (aleph_one_check_is_aleph_one_of_omega_lt (omega_lt_aleph_one)),
  { simp },
  { exact aleph_one_satisfies_universal_property }
end

lemma continuum_le_continuum_check {Γ : 𝔹} :
  Γ ≤ bv_powerset bSet.omega ≼ (pSet.powerset omega)̌ :=
begin
  refine injects_into_trans _ _, tactic.rotate 1, from powerset_injects_into_functions,
  have : Γ ≤ injects_into (functions pSet.omega (of_nat 2))̌  (powerset omega)̌ ,
    by { apply injects_into_of_is_injective_function,
         rcases functions_2_injects_into_powerset pSet.omega with ⟨f,Hf⟩,
         apply bv_use f̌, from check_is_injective_function Hf },
  change Γ ≤ (λ z, injects_into z (powerset omega)̌ ) _ at this,
  have := bv_rw'' _ this, tactic.rotate 2,
  apply check_functions_eq_functions, from ‹_›
end

lemma aleph_one_not_lt_powerset_omega : ∀ {Γ : 𝔹}, Γ ≤ - (ℵ₁̌ ≺ 𝒫(ω)) :=
begin
  intro Γ, rw[<-imp_bot], dsimp, bv_imp_intro H,
  refine bv_absurd _ ℵ₁_larger_than_continuum _,
  exact bSet_lt_of_lt_of_le _ _ _ H continuum_le_continuum_check
end

theorem CH_true : (⊤ : 𝔹) ≤ CH :=
CH_true_aux aleph_one_check_universal_property (by apply aleph_one_not_lt_powerset_omega)

theorem CH₂_true : (⊤ : 𝔹) ≤ CH₂ :=
le_inf (by apply aleph_one_not_lt_powerset_omega) (omega_lt_aleph_one)

end collapse_algebra
