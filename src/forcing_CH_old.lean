import .bvm_extras .collapse

/-
  Forcing the continuum hypothesis.
-/

universe u

open lattice bSet topological_space pSet cardinal

local infix ` ⟹ `:65 := lattice.imp

local infix ` ⇔ `:50 := lattice.biimp

local infix `≺`:70 := (λ x y, -(larger_than x y))

local infix `≼`:70 := (λ x y, injects_into x y)

@[reducible]private noncomputable definition ℵ₁ : pSet := (card_ex $ aleph 1)

local notation `ω` := (bSet.omega)

local attribute [instance, priority 0] classical.prop_decidable

section lemmas

variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

/-- Corresponds to proposition 5.2 in Moore's 'the method of forcing':
Let x be a set and let ϕ(v) be a formula in the forcing language. If ∀ y ∈ x, p ⊩ ϕ(y̌), then p ⊩ ∀ y ∈ (x̌), ϕ(y)
-/
lemma check_forall (x : pSet) (ϕ : bSet 𝔹 → 𝔹) {h : B_ext ϕ} {b : 𝔹} :
  (∀ (y : x.type), b ≤ ϕ((x.func y)̌ )) → (b ≤ (⨅(y : x.type), ϕ((x.func y)̌ ))) :=
λ H, le_infi ‹_›

lemma aleph_one_check_is_aleph_one_of_omega_lt {Γ : 𝔹} (H : Γ ≤ bSet.omega ≺ (ℵ₁)̌ ): Γ ≤ (ℵ₁̌ ) =ᴮ (aleph_one) :=
begin
  refine subset_ext aleph_one_check_sub_aleph_one _,
  have := @aleph_one_satisfies_Ord_spec _ _ Γ, unfold aleph_one_Ord_spec at this,
  bv_split, revert this_right, bv_split, intro this_right,
  from this_right (ℵ₁ ̌) (by simp) ‹_›
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
    { change B_ext _, from B_ext_term (B_ext_mem_left) (by simp) }
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
          { exact B_ext_term (B_ext_mem_left) (by simp) },
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
  refine le_inf (by apply rel_of_array_extensional; assumption) _,
  rw[<-bounded_forall], bv_intro i_x, bv_imp_intro Hi_x, rw[<-bounded_exists],
    { simp[*,rel_of_array, -Γ_1], rw[supr_comm, supr_prod],
      apply bv_use i_x,
      transitivity ⨆ (j : type y),
      af ((i_x, j).fst) ((i_x, j).snd) ⊓ pair (func x i_x) (func y j) =ᴮ pair (func x ((i_x, j).fst)) (func y ((i_x, j).snd)),
        { conv { to_rhs, funext, congr, funext,rw[bv_eq_refl] }, simp[H_tall]},
        { exact diagonal_supr_le_supr (by refl) }},
    { change B_ext _, from B_ext_term (B_ext_mem_left) (by simp) },
    { change B_ext _, apply B_ext_supr, intro, apply B_ext_inf,
      { simp },
      { from B_ext_term (B_ext_mem_left) (by simp) }}
end

end lemmas

namespace collapse_algebra

local notation `𝔹` := collapse_algebra ((ℵ₁ : pSet).type) (powerset omega : pSet).type
local prefix `#`:50 := cardinal.mk
local attribute [instance, priority 9001] collapse_space

open collapse_poset

lemma π_χ_regular (p : type (card_ex (aleph 1)) × (powerset omega).type) : @topological_space.is_regular _ collapse_space {g : type (card_ex (aleph 1)) → type (powerset omega) | g (p.fst) = p.snd} :=
by simp

def π_χ : ((ℵ₁ : pSet.{u}).type × (pSet.powerset omega : pSet.{u}).type) → 𝔹 :=
λ p, ⟨{g | g p.1 = p.2}, π_χ_regular _⟩

private lemma eq₀ : ((ℵ₁)̌  : bSet 𝔹).type = (ℵ₁).type := by simp

private lemma eq₀' : ((powerset omega)̌  : bSet.{u} 𝔹).type = (powerset omega).type := by simp

private lemma eq₁ : (((ℵ₁)̌  : bSet 𝔹).type × ((powerset omega)̌  : bSet 𝔹).type) = ((ℵ₁ .type) × (powerset omega).type) := by simp

lemma aleph_one_type_uncountable : (aleph 0) < # ℵ₁.type :=
by simp only [cardinal.aleph_zero, pSet.omega_lt_aleph_one, pSet.mk_type_mk_eq''']

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
by apply bv_use π; from π_spec'

-- for these two lemmas, need 2.17 (iv) in Bell, which follows from (i) ⟹ (ii)
-- i.e. If 𝔹 has a dense subset P which is ω-closed, then for any η < ℵ₁, and any x,
-- bSet 𝔹 ⊩ Func(η̌, x̌) = Func(η, x)̌ .

/-
Proof sketch:
Let p : P be such that p ⊩ f is a function from η̌ to x̌. Using the ω-closed assumption, find a descending sequence {p_i : P} and a set {y_i ∈ x} such that for each i, pᵢ ⊩ f(i) = y_i.

If q ∈ P satisfies q ≤ pᵢ for all i (i.e. is a witness to the ω-closed assumption),
and g is the function attached to the collection of pairs (i, y_i), show that q ⊩ f = ǧ.
-/

--TODO(jesse) finish this
-- lemma function_reflect_aux {y : pSet} (g : bSet 𝔹) (H : Γ ≤ is_func' (ω) (y̌))

lemma distributive {x : pSet} (H_inj : ∀ i₁ i₂ : x.type, pSet.equiv (x.func i₁) (x.func i₂) → i₁ = i₂) (af : pSet.omega.type → x.type → 𝔹) :
   ⨅ i : pSet.omega.type, (⨆ j : x.type, af i j) = ⨆(f : pSet.omega.type → x.type), ⨅(i : pSet.omega.type), af i (f i)
 := sorry

lemma functions_eq {x : pSet} (H_inj : ∀ i₁ i₂ : x.type, pSet.equiv (x.func i₁) (x.func i₂) → i₁ = i₂) : sorry := sorry

def function_reflect (y : pSet) (g : bSet 𝔹) {Γ} (H : Γ ≤  (is_function (ω) (y̌) g)) : pSet :=
mk (ulift ℕ) (λ k, sorry)

lemma function_reflect_spec₁ {y} {g} {Γ : 𝔹} (H : Γ ≤ _) : Γ ≤ (function_reflect y g H)̌  =ᴮ g :=
sorry

lemma function_reflect_spec₂ {y} {g} {Γ : 𝔹} (H : Γ ≤ _) : is_func pSet.omega y (function_reflect y g H) :=
sorry

lemma function_reflect_surj_of_surj {g} {y} {Γ : 𝔹} (H : Γ ≤ _) (H_not_zero : ⊥ < Γ) (H_surj : Γ ≤ is_surj ((omega)̌ ) (y̌) (g : bSet 𝔹)) :
  pSet.is_surj ((omega)) y (function_reflect y g H) :=
sorry -- TODO(jesse) this should be easy because surjectivity is Δ₀, so prove a general lemma for this

--TODO(jesse) update this proof with new is_function_of_is_func' lemmas
lemma omega_lt_aleph_one {Γ : 𝔹} : Γ ≤ bSet.omega ≺ (ℵ₁̌ ) :=
begin
  unfold larger_than, rw[<-imp_bot], rw[<-deduction], /- `tidy_context` says -/ refine poset_yoneda _, intros Γ_1 a, simp only [le_inf_iff] at *, cases a,
  bv_cases_at a_right f, rw[le_inf_iff] at a_right_1, cases a_right_1,
  by_contra, replace a := (bot_lt_iff_not_le_bot.mpr a),
  suffices this : ∃ f : pSet, is_func _ _ f ∧ pSet.is_surj (pSet.omega) (ordinal.mk (aleph 1).ord) f,
    by {exfalso, from pSet.ex_no_surj_omega_aleph_one this},
  let g := (function_reflect (card_ex $ aleph 1) f sorry), use g,
  refine ⟨_,_⟩,
    { apply function_reflect_spec₂ },
    { apply function_reflect_surj_of_surj, from ‹_›, from a_right_1_right }
end

lemma aleph_one_check_universal_property (Γ : 𝔹) : Γ ≤ aleph_one_weak_universal_property (ℵ₁̌  : bSet 𝔹) :=
begin
  apply bv_rw' (aleph_one_check_is_aleph_one_of_omega_lt (omega_lt_aleph_one)),
  { simp },
  { exact aleph_one_satisfies_universal_property }
end

lemma continuum_is_continuum {Γ : 𝔹} : Γ ≤ (pSet.powerset omega)̌  =ᴮ (bv_powerset bSet.omega) :=
begin
  refine subset_ext (check_powerset_subset_powerset _) _,
  bv_intro χ, bv_imp_intro H_χ,
  refine le_trans le_top _, rw[bSet.mem_unfold], simp only [check_bval_top, top_inf_eq],
  simp only [bv_eq_unfold],
  sorry
-- TOOD(jesse) show that this simplifies to ⨆_S ⨅ i, σ_S(i) (χ i), where σ_S(i) is the ¬-indicator function o S

-- then an inductively-defined version of S := {i | ¬ χ i ⊓ principal_open p = ⊥} should work
end

-- lemma continuum_is_continuum {Γ : 𝔹} : Γ ≤ (pSet.powerset omega)̌  =ᴮ (bv_powerset bSet.omega) :=
-- begin
--   refine subset_ext (check_powerset_subset_powerset _) _,
--   bv_intro χ, bv_imp_intro H_χ,
--   suffices this : ∃ S : (powerset omega).type, Γ_1 ≤  (set_of_indicator χ) =ᴮ ((powerset omega).func S)̌ ,
--     by { cases this with S HS, apply bv_use S, rwa[top_inf_eq] },
--   clear H_χ,
--   fsplit,
--     { sorry },
--     { rw[bv_eq_unfold], refine le_inf _ _,
--       { sorry }, -- this condition says that says for ∀ i, χ i ≤ ω.func i ∈ᴮ Š
--                  -- note that S, being a subtype, also satisfies a 0-1 property,
--                  -- so that ∀ i, (⊥ < (ω.func i ∈ᴮ Š) ↔ ⊤ = ω.func i ∈ᴮ Š ↔ (S i))
--                  -- so, in case that ⊥ < χ i, we must have that i ∈ S.

--       { sorry } -- this condition, combined some easy facts and check_mem_set_of_indicator_iff,
--                 -- says that S ⊆ {i | χ i = ⊤}
-- }
-- end

lemma aleph_one_not_lt_powerset_omega : ∀ {Γ : 𝔹}, Γ ≤ - (ℵ₁̌ ≺ 𝒫(ω)) :=
begin
 intro Γ, rw[<-imp_bot], bv_imp_intro H,
 suffices ex_surj : Γ_1 ≤ larger_than (ℵ₁̌ ) (𝒫 ω),
     by {dsimp [Γ_1] at H ex_surj ⊢, from bv_absurd _ ex_surj ‹_› },

      apply bv_rw' (bv_symm continuum_is_continuum),
        { from B_ext_larger_than_right },
        { from ℵ₁_larger_than_continuum }
end

theorem CH_true : (⊤ : 𝔹) ≤ CH :=
CH_true_aux aleph_one_check_universal_property (by apply aleph_one_not_lt_powerset_omega)

theorem CH₂_true : (⊤ : 𝔹) ≤ CH₂ :=
le_inf (by apply aleph_one_not_lt_powerset_omega) (omega_lt_aleph_one)

end collapse_algebra
