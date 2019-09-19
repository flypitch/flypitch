import .bvm_extras .collapse .aleph_one

/-
  Forcing the continuum hypothesis.
-/

universe u

open lattice bSet topological_space pSet cardinal

local infix ` ⟹ `:65 := lattice.imp

local infix ` ⇔ `:50 := lattice.biimp

local infix `≺`:75 := (λ x y, -(bSet.larger_than x y))

local infix `≼`:75 := (λ x y, bSet.injects_into x y)

@[reducible]private noncomputable definition ℵ₁ : pSet := (card_ex $ aleph 1)

local notation `ω` := (bSet.omega)

local attribute [instance, priority 0] classical.prop_decidable

namespace bSet

section aleph_one

variables {𝔹 : Type*} [nontrivial_complete_boolean_algebra 𝔹]

noncomputable def aleph_one : bSet 𝔹 := a1

lemma aleph_one_satisfies_spec {Γ : 𝔹} : Γ ≤ aleph_one_Ord_spec (aleph_one) :=
a1_spec

lemma aleph_one_check_sub_aleph_one {Γ : 𝔹} : Γ ≤ (pSet.card_ex (aleph 1))̌  ⊆ᴮ aleph_one :=
aleph_one_check_sub_aleph_one_aux a1_Ord a1_spec

lemma aleph_one_le_of_omega_lt {Γ : 𝔹} : Γ ≤ le_of_omega_lt (aleph_one) :=
a1_le_of_omega_lt

end aleph_one

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
  have := @bSet.aleph_one_satisfies_spec _ _ Γ, unfold aleph_one_Ord_spec at this,
  bv_split, bv_split_at this_right,
  refine this_right_right (ℵ₁ ̌) (by simp) _, dsimp at H, rw ←imp_bot at ⊢ H,
  bv_imp_intro H', refine H (larger_than_of_surjects_onto $ surjects_onto_of_injects_into ‹_› $ by simp),
end

theorem CH_true_aux
  (H_aleph_one : ∀{Γ : 𝔹}, Γ ≤ le_of_omega_lt (ℵ₁̌ ))
  (H_not_lt    : ∀{Γ : 𝔹}, Γ ≤ - ((ℵ₁)̌  ≺ 𝒫(ω)))
  : ∀{Γ : 𝔹}, Γ ≤ CH :=
begin
  intro Γ, unfold CH, rw ←imp_bot, bv_imp_intro H_CH,
  suffices H_aleph_lt_continuum : Γ_1 ≤ (ℵ₁)̌  ≺ 𝒫(ω),
    by {refine bv_absurd _ ‹Γ_1 ≤ (ℵ₁)̌  ≺ 𝒫(ω)› (by solve_by_elim) },
  bv_cases_at H_CH x Hx, bv_split_at Hx, bv_cases_at Hx_right y Hy,
  bv_split_at Hy, bv_split_at Hy_left,
  refine bSet_lt_of_lt_of_le _ Hy_right,
  refine bSet_lt_of_le_of_lt _ Hy_left_right,
  refine @H_aleph_one Γ_3 x Hx_left Hy_left_left
end

def rel_of_array (x y : bSet 𝔹) (af : x.type → y.type → 𝔹) : bSet 𝔹 :=
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
       { rw[rel_of_array], simp, erw[supr_comm],
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
    { simp[*,rel_of_array, -Γ_1], erw[supr_comm, supr_prod],
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

section function_reflect

variables {D : set 𝔹}
          (H_docs : dense_omega_closed_subset D)
          {y : pSet.{u}}
          {g : bSet 𝔹}
          {Γ : 𝔹}
          (H_nonzero : ⊥ < Γ)
          (H : Γ ≤ is_func' bSet.omega y̌ g)
          (AE : ∀ (x y : pSet) {f : bSet 𝔹} {Γ : 𝔹},
                  Γ ≤ is_func' x̌  y̌  f →
                    ⊥ < Γ →
                      ∀ (i : pSet.type x),
                        ∃ (j : pSet.type y) (Γ' : 𝔹) (H_nonzero' : ⊥ < Γ') (H_le : Γ' ≤ Γ),
                          Γ' ≤ is_func' x̌  y̌  f ∧ Γ' ≤ pair (pSet.func x i)̌  (pSet.func y j)̌  ∈ᴮ f ∧ Γ' ∈ D )


local notation `ae₀` := AE pSet.omega y H H_nonzero

local notation `aeₖ` := AE pSet.omega y

include y g Γ H_nonzero H AE

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

@[reducible]noncomputable def function_reflect.B : ℕ → 𝔹 := λ n, (function_reflect.fB H_nonzero H AE n).2.1

@[reducible]noncomputable def function_reflect.f : ℕ → y.type := λ n, (function_reflect.fB H_nonzero H AE n).1

lemma function_reflect.B_nonzero (n) : ⊥ < (function_reflect.B H_nonzero H AE n) :=
(function_reflect.fB H_nonzero H AE n).2.2.left

lemma function_reflect.B_is_func' (n) : (function_reflect.B H_nonzero H AE n) ≤ is_func' bSet.omega y̌ g :=
(function_reflect.fB H_nonzero H AE n).2.2.right

lemma function_reflect.B_unfold {n} : function_reflect.B H_nonzero H AE (n+1)
  = classical.some ((function_reflect.fB._main._proof_7 H_nonzero H AE n)) -- yuck
:=  rfl

lemma function_reflect.B_le {n} : (function_reflect.B H_nonzero H AE (n + 1)) ≤ function_reflect.B H_nonzero H AE n :=
begin
  rw function_reflect.B_unfold, let p := _, change classical.some p ≤ _,
  rcases classical.some_spec p with ⟨_,_,_,_⟩, convert h_w, clear_except, unfold function_reflect.B, cases n, refl, refl,
end

lemma function_reflect.B_pair {n} : (function_reflect.B H_nonzero H AE n) ≤ pair (pSet.omega.func (ulift.up n))̌  (y.func $ function_reflect.f H_nonzero H AE n)̌  ∈ᴮ g :=
begin
  cases n,
    { change classical.some _ ≤ _, let p := _, change classical.some p ≤ _,
      rcases classical.some_spec p with ⟨_,_,_,_,_⟩, from ‹_› },
    { rw function_reflect.B_unfold, let p := _, change classical.some p ≤ _,
      rcases classical.some_spec p with ⟨_,_,_,_,_⟩, from ‹_› }
end

lemma function_reflect.B_mem_dense {n} : (function_reflect.B H_nonzero H AE n) ∈ D :=
begin
  cases n,
    { let p := _, change classical.some p ∈ _,
      rcases classical.some_spec p with ⟨_,_,_,_,_⟩, from ‹_› },
    { rw function_reflect.B_unfold, let p := _, change classical.some p ∈ _,
      rcases classical.some_spec p with ⟨_,_,_,_,_⟩, from ‹_› }
end

variable (H_function : Γ ≤ is_function bSet.omega y̌ g)

lemma function_reflect.B_infty_le_Γ : (⨅ n, (function_reflect.B H_nonzero H AE n)) ≤ Γ :=
begin
  refine infi_le_of_le 0 _, let p := _, change classical.some p ≤ _,
  rcases classical.some_spec p with ⟨_,_,_,_⟩, from ‹_›
end

lemma function_reflect_aux : (⨅n, function_reflect.B H_nonzero H AE n) ≤ (⨅n, pair (pSet.omega.func (ulift.up n))̌  (y.func $ function_reflect.f H_nonzero H AE n)̌  ∈ᴮ g) :=
infi_le_infi $ λ _, by apply function_reflect.B_pair

noncomputable def function_reflect.f' : pSet.{u} :=
begin
  refine @pSet.function.mk pSet.omega _ _,
  intro k, cases k with k',
  exact y.func (function_reflect.f H_nonzero H AE k'),
  intros i j Heqv,
  suffices this : i = j,
    by { subst this },
  from pSet.omega_inj ‹_›
end

lemma function_reflect.f'_is_function : ∀ {Γ : 𝔹}, Γ ≤ is_function (pSet.omega)̌  y̌ (function_reflect.f' H_nonzero H AE)̌  :=
begin
  refine @check_is_func 𝔹 _ pSet.omega y (function_reflect.f' H_nonzero H AE) _, apply pSet.function.mk_is_func, intro i, cases i, simp
end

lemma function_reflect_aux₂ : (⨅n, function_reflect.B H_nonzero H AE n) ≤ (⨅n, (pair (pSet.omega.func (ulift.up n))̌  (y.func $ function_reflect.f H_nonzero H AE n)̌  ∈ᴮ (function_reflect.f' H_nonzero H AE)̌  ⇔ (pair (pSet.omega.func (ulift.up n))̌  (y.func $ function_reflect.f H_nonzero H AE n)̌  ∈ᴮ g))) :=
begin
  refine infi_le_infi (λ n, _), tidy_context, refine ⟨_,_⟩; bv_imp_intro H_mem,
    { refine le_trans a _, apply function_reflect.B_pair },
    { apply @bv_rw' _ _ _ _ _ (bv_symm check_pair) (λ z, z ∈ᴮ  (function_reflect.f' H_nonzero H AE)̌ ), simp,
      refine check_mem _, convert pSet.function.mk_mem, refl }
end

include H_function

lemma function_reflect.B_infty_le_function : (⨅ n, (function_reflect.B H_nonzero H AE n)) ≤ is_function ω y̌ g :=
le_trans (by apply function_reflect.B_infty_le_Γ) H_function

lemma function_reflect_aux₃ : (⨅n, function_reflect.B H_nonzero H AE n) ≤ ⨅ (p : bSet 𝔹), p ∈ᴮ prod pSet.omegǎ  y̌  ⟹ (p ∈ᴮ (function_reflect.f' H_nonzero H AE)̌  ⇔ p ∈ᴮ g) :=
begin
  rw ←bounded_forall, swap, {change B_ext _, simp},
  bv_intro pr, rcases pr with ⟨⟨i⟩, j⟩, simp only [prod_check_bval, top_imp, prod_func],
  have := (function_reflect_aux₂ H_nonzero H AE) i, bv_split_at this,
  refine le_inf _ _; bv_imp_intro H',
    { have this' : Γ_1 ≤ (pair (func pSet.omegǎ  {down := i}) (func y̌  j)) =ᴮ (pair (pSet.func pSet.omega {down := i})̌  (pSet.func y (function_reflect.f H_nonzero H AE i))̌ ),
        by {rw pair_eq_pair_iff, refine ⟨bv_refl, _⟩,
            refine eq_of_is_func'_of_eq (is_func'_of_is_function _) _ _ _, show _ ≤ is_function bSet.omega y̌ (function_reflect.f' H_nonzero H AE)̌ ,
            refine check_is_func _, apply pSet.function.mk_is_func, intro n, cases n, simp,
            show _ ≤ _ =ᴮ _, apply bv_refl, from H',
            refine this_right _,
            refine le_trans (inf_le_right) (infi_le_of_le i (by apply function_reflect.B_pair))},
      apply @bv_rw' _ _ _ _ _ this' (λ z, z ∈ᴮ g), simp,
      have := (inf_le_right : Γ_1 ≤ _),
      exact le_trans this (le_trans
              (by apply function_reflect_aux) (infi_le_of_le i (by refl)))},
    { have this' : Γ_1 ≤ (pair (func pSet.omegǎ  {down := i}) (func y̌  j)) =ᴮ (pair (pSet.func pSet.omega {down := i})̌  (pSet.func y (function_reflect.f H_nonzero H AE i))̌ ),
        by {rw pair_eq_pair_iff, refine ⟨bv_refl, _⟩,
            refine eq_of_is_func'_of_eq (is_func'_of_is_function _) _ _ _, show _ ≤ is_function _ _ _, refine le_trans inf_le_right (function_reflect.B_infty_le_function _ _ _ H_function),
            show _ ≤ _ =ᴮ _, from (bv_refl : _ ≤ (func pSet.omegǎ  {down := i}) =ᴮ _), from H',
        refine le_trans (inf_le_right) (infi_le_of_le i _), apply function_reflect.B_pair },
      apply @bv_rw' _ _ _ _ _ this' (λ z, z ∈ᴮ ((function_reflect.f' H_nonzero H AE)̌ )), simp,
      apply @bv_rw' _ _ _ _ _ (bv_symm check_pair) (λ z, z ∈ᴮ  (function_reflect.f' H_nonzero H AE)̌ ), simp,
      refine check_mem _, convert pSet.function.mk_mem, refl}
end

include H_docs
lemma function_reflect_of_omega_closed : ∃ (f : pSet.{u}) (Γ' : 𝔹) (H_nonzero' : ⊥ < Γ') (H_le' : Γ' ≤ Γ), (Γ' ≤ f̌ =ᴮ g) ∧ pSet.is_func pSet.omega y f :=
begin
  refine ⟨function_reflect.f' H_nonzero H AE,_⟩,
    { use (⨅ n, function_reflect.B H_nonzero H AE n), -- this is Γ'
      refine ⟨_,_,⟨_,_⟩⟩,
        { apply nonzero_infi_of_mem_dense_omega_closed_subset, apply H_docs, apply function_reflect.B_le,
          apply function_reflect.B_mem_dense  },
        { refine infi_le_of_le 0 _, let p := _, change classical.some p ≤ _,
          rcases classical.some_spec p with ⟨_,_,_,_⟩, from ‹_› },
        { apply bSet.funext, apply function_reflect.f'_is_function,
          refine le_trans _ H_function, {exact function_reflect.B_infty_le_Γ H_nonzero H AE},
          apply function_reflect_aux₃, from ‹_› },
          { apply pSet.function.mk_is_func, intro n, cases n, simp }
    }
end

end function_reflect

end lemmas

end bSet

namespace collapse_algebra

open bSet

local prefix `#`:50 := cardinal.mk
local attribute [instance] collapse_space

open collapse_poset

def 𝔹_collapse : Type u := collapse_algebra ((ℵ₁ : pSet.{u}).type) (powerset omega : pSet.{u}).type

attribute instance 𝔹_collapse_boolean_algebra : nontrivial_complete_boolean_algebra 𝔹_collapse := by {unfold 𝔹_collapse, apply_instance}

local notation `β` := 𝔹_collapse

section AE_of_check_func_check'

local notation `ι` := (collapse_poset.inclusion : _ → 𝔹_collapse)

local attribute [irreducible] regular_open_algebra

lemma nonzero_wit'' {𝓑 : Type*} [nontrivial_complete_boolean_algebra 𝓑] {D : set 𝓑}
   (H_docs : dense_omega_closed_subset D) {I : Type*} {s : I → 𝓑} {Γ : 𝓑}
  (H_nonzero : ⊥ < Γ) (H_le : Γ ≤ ⨆ i , s i ):
  ∃ (j) (Γ' : 𝓑) (H_nonzero' : ⊥ < Γ') (H_le' : Γ' ≤ s j ⊓ Γ), Γ' ∈ D :=
begin
  have := nonzero_wit' H_nonzero H_le,
  cases this with j Hj,
  have := H_docs.left, rcases this with ⟨H_dense₁, H_dense₂⟩,
  specialize H_dense₂ _ Hj, rcases H_dense₂ with ⟨Γ', HΓ'₁, HΓ'₂⟩,
  use j, use Γ', use (nonzero_of_mem_dense_omega_closed_subset H_docs ‹_›),
  use ‹_›, from ‹_›
end

lemma AE_of_check_func_check' (x y : pSet) {f : bSet (collapse_algebra (type ℵ₁) (type (powerset omega)))}
  {Γ : collapse_algebra (type ℵ₁) (type (powerset omega))}
   (H :  Γ ≤ is_func' x̌  y̌  f)
    (H_nonzero : ⊥ < Γ )
    (i : type x) :
      ∃ (j : type y) (Γ' : collapse_algebra (type ℵ₁) (type (powerset omega))) (H_nonzero' : ⊥ < Γ')
        (H_le : Γ' ≤ Γ),
        Γ' ≤ is_func' x̌  y̌  f ∧
          Γ' ≤ pair (func x i)̌  (func y j)̌  ∈ᴮ f ∧ Γ' ∈ set.range ι :=
begin
  have := is_total_of_is_func' H ((x.func i)̌ ) (by simp),

  have H' : Γ ≤ (is_func' (x̌) (y̌) f) ⊓ ⨆ w, w ∈ᴮ (y̌) ⊓ pair (x.func i)̌  w ∈ᴮ f ,
    by exact le_inf ‹_› ‹_›,
  erw[←bounded_exists] at H', swap, {exact B_ext_pair_mem_right},
  rw[inf_supr_eq] at H',
  cases y, dsimp at H', simp only [top_inf_eq] at H',
  have := nonzero_wit'' principal_opens_dense_omega_closed H_nonzero H',
  rcases this with ⟨j,Γ', Γ'_nonzero, Γ'_le, HΓ'⟩,
  use j, use Γ', use ‹_›, bv_split_at Γ'_le, use ‹_›, bv_split_at Γ'_le_left,
  from ⟨‹_›,‹_›,‹_›⟩
end


end AE_of_check_func_check'

lemma check_functions_eq_functions (y : pSet.{u})
  {Γ : β} : Γ ≤ check (functions (pSet.omega) y) =ᴮ functions (bSet.omega) y̌ :=
begin
  refine subset_ext check_functions_subset_functions _,
  rw[subset_unfold'], bv_intro g, bv_imp_intro Hg, rw[mem_unfold'],
  let A := _, change _ ≤ A, let B := _, change _ ≤ B at Hg,
  suffices this : A ⊓ B = B,
    by {refine le_trans _ inf_le_left, from B, rw this, simp* },
  apply Sup_eq_top_of_dense_Union_rel, apply rel_dense_of_dense_in_basis B.1 _ collapse_space_basis_spec,
  intros D HD HD_ne, unfold collapse_space_basis at HD, cases HD with p Hp,
    { clear_except p HD_ne, exfalso, finish },
    rcases Hp with ⟨p,⟨_,Hp⟩⟩, subst Hp, let P : β := ⟨principal_open p, is_regular_principal_open p⟩,
    have bot_lt_Γ : (⊥ : β) < P ⊓ B,
    rw [bot_lt_iff_not_le_bot, le_bot_iff], rwa subtype.ext,
    have := function_reflect_of_omega_closed principal_opens_dense_omega_closed bot_lt_Γ
      (by {dsimp[B], refine inf_le_right_of_le (is_func'_of_is_function
            (by { refine poset_yoneda _, tactic.rotate 2, intros Γ HΓ, rw[bSet.mem_functions_iff] at HΓ, convert HΓ }))}) _ (by {dsimp [B],
              refine poset_yoneda _, intros Γ HΓ, exact bSet.mem_functions_iff.mp (bv_and.right HΓ) }),
    rcases this with ⟨f, Γ', H_nonzero', H_lt', H_pr', H_func'⟩, apply set.inter_sUnion_ne_empty_of_exists_mem,
    let C := g ∈ᴮ (functions omega y)̌  ⊓ g =ᴮ g,
    use C.val, simp, refine ⟨⟨C.property, _⟩, _⟩, use g,
    suffices this : P ⊓ B ⊓ C ≠ ⊥,
      by {change ¬ _ at this, rwa subtype.ext at this }, rw ←bot_lt_iff_ne_bot,
    suffices this : Γ' ≤ C,
      by {exact lt_of_lt_of_le H_nonzero' (le_inf ‹_› ‹_›)},
    refine le_inf _ (bv_refl), apply bv_rw' (bv_symm H_pr'), simp,
    rw ←pSet.mem_functions_iff at H_func', from check_mem H_func',
    exact AE_of_check_func_check'
end

lemma π_χ_regular (p : type (card_ex (aleph 1)) × (powerset omega).type) : @topological_space.is_regular _ collapse_space {g : type (card_ex (aleph 1)) → type (powerset omega) | g (p.fst) = p.snd} :=
by simp

def π_χ : ((ℵ₁ : pSet.{u}).type × (pSet.powerset omega : pSet.{u}).type) → β :=
λ p, ⟨{g | g p.1 = p.2}, π_χ_regular _⟩

private lemma eq₀ : ((ℵ₁)̌  : bSet β).type = (ℵ₁).type := by simp

private lemma eq₀' : ((powerset omega)̌  : bSet.{u} β).type = (powerset omega).type := by simp

private lemma eq₁ : ((ℵ₁̌  : bSet β).type × ((powerset omega)̌  : bSet β).type) = ((ℵ₁).type × (powerset omega : pSet.{u}).type ):= by simp

lemma aleph_one_type_uncountable : cardinal.omega.succ ≤ # ℵ₁.type :=
by simp only [succ_le, pSet.omega_lt_aleph_one, pSet.mk_type_mk_eq''']

@[reducible]def π_af : ((ℵ₁̌  : bSet β) .type) → ((powerset omega)̌  : bSet β) .type → β :=
λ η S, (⟨{g | g (cast eq₀ η) = (cast eq₀' S)}, by simp⟩ : β)

lemma π_af_wide :  ∀ (j : ((powerset omega)̌ ).type), (⨆ (i : type (ℵ₁̌ )), π_af i j) = (⊤ : β) :=
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
     use p.f.trivial_extension S, use trivial_extension_mem_principal_open,
     change ∃ x, _, use (π_af (cast eq₀.symm η) S).val,
     refine ⟨_, _⟩, change ∃ x, _, refine ⟨_,_⟩,
     apply π_af (cast eq₀.symm η) S, refine ⟨_,_⟩,
       { exact set.mem_range_self _ },
       { refl },
     { unfold pfun.trivial_extension pfun.extend_via, dsimp,
       suffices this : (cast eq₀ (cast eq₀.symm η) ∉ pfun.dom (p.f)),
         by {simpa*},
       intro, apply Hη, cc } }
end

lemma π_af_tall : ∀ (i : (card_ex $ aleph 1)̌ .type), (⨆(j : (powerset omega)̌ .type), π_af i j) = (⊤ : β) :=
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

lemma π_af_anti : ∀ (i : type (ℵ₁̌  : bSet β)) (j₁ j₂ : type ((powerset omega)̌ )),
    j₁ ≠ j₂ → π_af i j₁ ⊓ π_af i j₂ ≤ ⊥ :=
λ _ _ _ _ _ h, by cases h; finish

lemma check_index_inj_of_pSet_index_inj {x : pSet.{u}} (H_inj : ∀ i₁ i₂ : x.type, pSet.equiv (x.func i₁) (x.func i₂) → i₁ = i₂) : ∀ i₁ i₂ : (x̌ : bSet β).type, ⊥ < x̌.func i₁ =ᴮ x̌.func i₂ → i₁ = i₂ :=
begin
  have : ∀ i₁ i₂ : x.type, i₁ ≠ i₂ → ¬ equiv (func x i₁) (func x i₂),
    by finish,
  {intros i₁ i₂ H, haveI : decidable (i₁ = i₂) := classical.prop_decidable _,
        by_contra,
        have H_cast_eq : (check_cast i₁) ≠ (check_cast i₂),
          by { intro H_eq, apply a, unfold check_cast at H_eq, cc },
        specialize this (check_cast i₁) (check_cast i₂) ‹_›,
        have this₀ := check_bv_eq_bot_of_not_equiv this,
        suffices this₁ : x̌.func i₁ =ᴮ x̌.func i₂ = ⊥,
          by {exfalso, rw[eq_bot_iff] at this₀, rw[bot_lt_iff_not_le_bot] at H,
              suffices : x̌.func i₁ =ᴮ x̌.func i₂ ≤ ⊥, by contradiction,
              convert_to (func x (check_cast i₁))̌   =ᴮ (func x (check_cast i₂)) ̌ ≤ ⊥,
              apply check_func, apply check_func, from ‹_›},
        convert this₀; apply check_func}
end

lemma aleph_one_inj : (∀ i₁ i₂, ⊥ < (func (ℵ₁̌  : bSet β) i₁) =ᴮ (func (ℵ₁̌  : bSet β) i₂) → i₁ = i₂) :=
check_index_inj_of_pSet_index_inj $
  by {intros _ _ H, contrapose H, apply ordinal.mk_inj, from ‹_› }

noncomputable def π : bSet β :=
rel_of_array (ℵ₁̌  : bSet β) ((powerset omega)̌ ) π_af

lemma π_is_func {Γ} : Γ ≤ is_func π :=
begin
  unfold π, refine rel_of_array_extensional _ _ _ (by simp) (by simp) _ _ _,
  { from π_af_wide },
  { from π_af_anti },
  { from aleph_one_inj },
end

lemma π_is_func' {Γ} : Γ ≤ is_func' (ℵ₁̌  : bSet β) ((powerset omega)̌ ) π :=
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

lemma π_spec {Γ : β} : Γ ≤ (is_func π) ⊓ ⨅v, v ∈ᴮ (powerset omega)̌  ⟹ (⨆w, w ∈ᴮ (ℵ₁̌ ) ⊓ pair w v ∈ᴮ π) := le_inf π_is_func π_is_surj

lemma π_spec' {Γ : β} : Γ ≤ (is_func' ((card_ex $ aleph 1)̌ ) ((powerset omega)̌ ) π) ⊓ is_surj ((card_ex $ aleph 1)̌ ) ((powerset omega)̌ ) π:=  le_inf π_is_func' π_is_surj

lemma ℵ₁_larger_than_continuum {Γ : β} : Γ ≤ larger_than (ℵ₁ ̌) ((powerset omega)̌ ) :=
by { apply bv_use (ℵ₁ ̌), apply bv_use π, rw[inf_assoc], from le_inf subset_self π_spec' }

lemma surjection_reflect {Γ : β} (H_bot_lt : ⊥ < Γ) (H_surj : Γ ≤ surjects_onto (bSet.omega : bSet.{u} β) ((ℵ₁)̌  : bSet β))
: ∃ (f : pSet.{u}), is_func omega (ordinal.mk (ord (aleph 1))) f
   ∧ is_surj pSet.omega (card_ex $ aleph 1) f :=
begin
  by_contra H, simp only [not_exists, not_and_distrib] at H,
  suffices this : Γ ≤ ⊥,
    by {rw[bot_lt_iff_not_le_bot] at H_bot_lt, contradiction},
  have := exists_surjection_of_surjects_onto H_surj,
  bv_cases_at this f Hf, bv_split_at Hf,
  rw[<-bSet.mem_functions_iff] at Hf_left,
  suffices this : Γ_1 ≤ f ∈ᴮ (pSet.functions pSet.omega (ℵ₁))̌ ,
    by { by_contra H', rw[<-bot_lt_iff_not_le_bot] at H',
         replace this := eq_check_of_mem_check H' this,
         rcases this with ⟨i_g, Γ', H₁,H₂,H₃⟩,
         apply_at Hf_right le_trans H₂,
         apply_at Hf_left le_trans H₂,
         let g := (pSet.functions pSet.omega ℵ₁).func i_g,
         specialize H g, cases H,
           { apply_at H check_not_is_func, show β, from Γ',
           rw[bSet.mem_functions_iff] at Hf_left,
           tactic.rotate 1, apply_instance,
           refine false_of_bot_lt_and_le_bot H₁ (H _),

           change Γ' ≤ f =ᴮ ǧ at H₃, apply_at H₃ bv_symm,
           apply bv_rw' H₃, simp, from Hf_left },
           { apply_at H check_not_is_surj,  show β, from Γ',
           tactic.rotate 1, apply_instance,
           refine false_of_bot_lt_and_le_bot H₁ (H _),
           change Γ' ≤ f =ᴮ ǧ at H₃, apply_at H₃ bv_symm,
           apply bv_rw' H₃, simp, from Hf_right}
         },
  have : Γ_1 ≤ _,
    from check_functions_eq_functions ℵ₁,
  bv_cc
end

lemma omega_lt_aleph_one {Γ : β} : Γ ≤ bSet.omega ≺ (ℵ₁̌ ) :=
begin
  unfold larger_than, rw[<-imp_bot, <-deduction],
  /- `tidy_context` says -/ refine poset_yoneda _, intros Γ_1 a, simp only [le_inf_iff] at *, cases a,
  bv_cases_at a_right S HS, apply lattice.context_Or_elim HS,
  intros f Hf, specialize_context Γ_2,
  simp only [le_inf_iff] at Hf, repeat{auto_cases}, by_contra H,
  replace H := (bot_lt_iff_not_le_bot.mpr H),
  suffices : ∃ f : pSet, is_func pSet.omega (ordinal.mk (aleph 1).ord) f ∧ pSet.is_surj (pSet.omega) (ordinal.mk (aleph 1).ord) f,
    by {exfalso, from ex_no_surj_omega_aleph_one ‹_›},
  suffices : Γ_3 ≤ surjects_onto ω ℵ₁̌ ,
    by {from surjection_reflect H this},
  refine surjects_onto_of_larger_than_and_exists_mem ‹_› (by simp),
end

lemma aleph_one_check_le_of_omega_lt (Γ : β) : Γ ≤ le_of_omega_lt (ℵ₁̌  : bSet β) :=
begin
  apply bv_rw' (aleph_one_check_is_aleph_one_of_omega_lt (omega_lt_aleph_one)),
  { simp },
  { exact aleph_one_le_of_omega_lt }
end

lemma continuum_le_continuum_check {Γ : β} :
  Γ ≤ bv_powerset (bSet.omega : bSet β) ≼ (pSet.powerset (pSet.omega : pSet.{u}) : pSet.{u})̌ :=
begin
    refine injects_into_trans _ _, tactic.rotate 1, from powerset_injects_into_functions,
  have : (Γ : β) ≤ injects_into (functions pSet.omega (of_nat 2) : pSet.{u})̌  (powerset (omega) : pSet.{u})̌ ,
    by { rw injects_into_iff_injection_into,
         rcases functions_2_injects_into_powerset (pSet.omega : pSet.{u}) with ⟨f,Hf⟩,
         apply bv_use f̌, refine check_is_injective_function _, from Hf
 },
  change Γ ≤ (λ z, injects_into z (powerset omega)̌ ) _ at this,
  have := bv_rw'' _ this, tactic.rotate 2,
  exact check_functions_eq_functions (of_nat 2),
  from this
end

lemma aleph_one_not_lt_powerset_omega : ∀ {Γ : β}, Γ ≤ - (ℵ₁̌ ≺ 𝒫(ω)) :=
begin
  intro Γ, rw[<-imp_bot], dsimp, bv_imp_intro H,
  refine bv_absurd _ ℵ₁_larger_than_continuum _,
  exact bSet_lt_of_lt_of_le H continuum_le_continuum_check
end

theorem CH_true : (⊤ : β) ≤ CH :=
CH_true_aux aleph_one_check_le_of_omega_lt (by apply aleph_one_not_lt_powerset_omega)

theorem CH₂_true : (⊤ : β) ≤ CH₂ :=
CH_iff_CH₂.mp CH_true

end collapse_algebra
