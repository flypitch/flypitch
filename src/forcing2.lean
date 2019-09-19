-- import pSet_ordinal bvm bvm_extras cantor_space

-- open ordinal cardinal lattice bSet

-- noncomputable theory

-- local attribute [instance] classical.prop_decidable

-- local attribute [simp] omega_le_aleph

-- local infix ` ⟹ `:65 := lattice.imp

-- local infix ` ⇔ `:50 := lattice.biimp

-- local prefix `#`:70 := cardinal.mk

-- universe u

-- namespace bSet
-- section cardinal_preservation
-- local notation `ω` := cardinal.omega
-- variables {𝔹 : Type u} [I : nontrivial_complete_boolean_algebra 𝔹]

-- include I
-- lemma AE_of_check_larger_than_check (x y : pSet.{u}) {f : bSet 𝔹} {Γ}
--   (H : Γ ≤ (is_func f) ⊓ ⨅v, v ∈ᴮ y̌ ⟹ ⨆w, w ∈ᴮ x̌ ⊓ pair w v ∈ᴮ f) (h_nonzero : ⊥ < Γ) :
--   ∀ i : y.type, ∃ j : x.type, ⊥ < (is_func f) ⊓ (pair ((x.func j)̌ ) ((y.func i)̌ )) ∈ᴮ f :=
-- begin
--   intro i_v, bv_split_at H, replace H_1_1 := H_1_1 ((y.func i_v)̌ ), simp[check_mem'] at H_1_1,
--   have H' : Γ ≤ is_func f ⊓ ⨆ (w : bSet 𝔹), w ∈ᴮ x̌  ⊓ pair w (pSet.func y i_v̌)  ∈ᴮ f,
--     from context_and_intro ‹_› ‹_›,
--   rw[inf_supr_eq] at H',
--   replace H' := le_trans H' (by {apply supr_le, intro i, recover, show 𝔹,
--     from ⨆ (i : bSet 𝔹), i ∈ᴮ x̌ ⊓ (is_func f ⊓ pair i (pSet.func y i_v̌)  ∈ᴮ f),
--     apply bv_use i, apply le_of_eq, ac_refl}),
--   replace H' := lt_of_lt_of_le h_nonzero H',
--   have := @bounded_exists 𝔹 _ (x̌) (λ z, is_func f ⊓ pair z ((y.func i_v)̌ ) ∈ᴮ f),
--   rw[<-this] at H', swap,
--     {intros x' y',
--     apply poset_yoneda, intros Γ_1 a,
--     simp only [le_inf_iff] at a H ⊢, cases a, cases H, cases a_right, refine ⟨‹_›, _⟩,
--     have : Γ_1 ≤ pair x' ((y.func i_v)̌ ) =ᴮ pair y' ((y.func i_v)̌ ),
--      from subst_congr_pair_left' ‹_›, apply subst_congr_mem_left'; from ‹_›},
--     {cases x, cases y, convert nonzero_wit H', ext1,
--       dsimp with cleanup, rw[top_inf_eq]}
-- end

-- variables
--   (η₁ η₂ : pSet.{u}) (H_infinite : ω ≤ #(η₁.type))
--   (H_lt : #(η₁.type) < #(η₂.type))
--   (H_inj₂ : ∀ x y, x ≠ y → ¬ pSet.equiv (η₂.func x) (η₂.func y))
--   (f : bSet 𝔹) (g : η₂.type → η₁.type)
--   (H : ∀ β : η₂.type, (⊥ : 𝔹) < is_func f ⊓ pair ((η₁.func (g β)̌ ) ) ((η₂.func β)̌ )∈ᴮ f)

-- include H_infinite H_lt H_inj₂ f H
-- lemma not_CCC_of_uncountable_fiber (H_ex : ∃ ξ : η₁.type, ω < #(g⁻¹' {ξ})) : ¬ CCC 𝔹 :=
-- begin
--   cases H_ex with ξ H_ξ,
--   let 𝓐 : (g⁻¹'{ξ}) → 𝔹 :=
--     λ β, is_func f ⊓ (pair ((η₁.func (g β.val))̌ ) ((η₂.func β.val)̌ )) ∈ᴮ f,
--   have 𝓐_nontriv : ∀ β, ⊥ < 𝓐 β,
--     from λ _, by apply H,
--   have 𝓐_anti : ∀ β₁ β₂, β₁ ≠ β₂ → (𝓐 β₁) ⊓ (𝓐 β₂) ≤ ⊥,
--     by {intros β₁ β₂ h_sep, dsimp[𝓐],
--     /- `tidy_context` says -/ apply poset_yoneda, intros Γ a,
--     cases β₂, cases β₁, cases H_ξ, cases H_lt, cases β₁_property, cases β₂_property,
--     work_on_goal 0 { induction β₂_property, simp only [le_inf_iff] at a,
--                      cases a, cases a_right, cases a_left },
--     work_on_goal 1 { induction β₁_property, simp only [le_inf_iff] at a,
--                      cases a, cases a_right, cases a_left, solve_by_elim },
--     work_on_goal 1 { cases β₂_property,
--       work_on_goal 0 { induction β₂_property, simp only [le_inf_iff] at a,
--         cases a, cases a_right, cases a_left, solve_by_elim}, simp only [le_inf_iff] at a,
--         cases a, cases a_right, cases a_left, solve_by_elim},

--     rw[β₁_property] at a_left_right,
--     have H_le_eq : Γ ≤ ((η₂.func β₁_val)̌ ) =ᴮ ((η₂.func β₂_val)̌ ),
--      by {apply funext; from ‹_›},
--     from le_trans H_le_eq
--            (by {rw[le_bot_iff], apply check_bv_eq_bot_of_not_equiv, apply H_inj₂, tidy})},
--    intro H_CCC, specialize H_CCC (g⁻¹'{ξ}) ‹_› ‹_› ‹_›,
--    replace H_ξ := (lt_iff_le_and_ne.mp H_ξ),
--    from absurd (le_antisymm H_ξ.left H_CCC) H_ξ.right
-- end

-- end cardinal_preservation
-- end bSet


-- open bSet pSet


-- namespace cohen_algebra

-- section cohen_algebra
-- variables (κ : cardinal.{u})

-- instance H_nonempty' : nonempty (set $ (card_ex κ).type × ℕ) := ⟨∅⟩

-- def cohen_algebra := @regular_opens (set ((card_ex κ).type × ℕ)) (Pi.topological_space)

-- @[instance, priority 1000]def cohen_algebra_boolean_algebra : nontrivial_complete_boolean_algebra (cohen_algebra κ) :=
-- regular_open_algebra (by apply_instance)

-- lemma le_iff_subset'' {x y : (cohen_algebra κ)} : x ≤ y ↔ x.1 ⊆ y.1 := by refl

-- lemma bot_eq_empty : (⊥ : (cohen_algebra κ)) = ⟨∅, is_regular_empty⟩ := rfl

-- variable{κ}
-- lemma eq₀ : ((card_ex κ)̌  : bSet (cohen_algebra κ)).type = ((card_ex κ)).type := by cases (card_ex κ); refl


-- lemma eq₁ : ((type ((card_ex κ)̌  : bSet (cohen_algebra κ))) × ℕ) = ((type (card_ex κ)) × ℕ) :=
-- by {cases (card_ex κ), refl}


-- lemma eq₂ : set ((type ((card_ex κ)̌  : bSet (cohen_algebra κ))) × ℕ) = set ((type (card_ex κ)) × ℕ) :=
-- by {cases (card_ex κ), refl}


-- lemma eq₃ : finset ((type ((card_ex κ)̌  : bSet (cohen_algebra κ))) × ℕ) = finset (type (card_ex κ) × ℕ) :=
-- by {cases (card_ex κ), refl}


-- lemma pi₂_cast₁ {α β γ : Type*} (H' : α = β) {p : α × γ} {q : β × γ} (H : p == q) :
--   p.1 == q.1 :=
-- by {subst H', subst H}


-- lemma pi₂_cast₂ {α β γ : Type*} (H' : α = β) {p : α × γ} {q : β × γ} (H : p == q) :
--   p.2 = q.2 :=
-- by {subst H', subst H}

-- lemma compl_cast₂ {α β : Type*} {a : set α} {b : set β} (H' : α = β) (H : -a == b) : a == -b :=
-- begin
--   subst H', subst H, apply heq_of_eq, simp
-- end

-- lemma eq₁_cast (p : ((type ((card_ex κ)̌  : bSet (cohen_algebra κ))) × ℕ)) {prf : ((type ((card_ex κ)̌  : bSet (cohen_algebra κ))) × ℕ) = (((type (card_ex κ)) × ℕ))} {prf' : (type ((card_ex κ)̌  : bSet (cohen_algebra κ))) = ((card_ex κ).type)} : cast prf p = (cast prf' p.1, p.2) :=
-- begin
--   ext, swap, simp, h_generalize H_x : p == x, apply pi₂_cast₂, from (eq₀).symm, from H_x.symm,
--   h_generalize H_x : p == x, simp, h_generalize H_y : p.fst == y,
--   apply eq_of_heq, suffices : x.fst == p.fst, from heq.trans this H_y,
--   apply pi₂_cast₁, from (eq₀).symm, from H_x.symm
-- end

-- -- lemma eq₁_cast' {ξ : ((card_ex κ)̌  : bSet (cohen_algebra κ)).type} {n : ℕ} {prf : ((type ((card_ex κ)̌  : bSet (cohen_algebra κ))) × ℕ) = (((type (card_ex κ)) × ℕ))} {prf' : (type ((card_ex κ)̌  : bSet (cohen_algebra κ))) = ((card_ex κ).type)} : cast prf (ξ, n) = (cast prf' ξ, n) :=
-- -- by apply eq₁_cast

-- lemma eq₁_cast' (p : (((type (card_ex κ)) × ℕ))) {prf : ((type ((card_ex κ)̌  : bSet (cohen_algebra κ))) × ℕ) = (((type (card_ex κ)) × ℕ))} {prf' : (type ((card_ex κ)̌  : bSet (cohen_algebra κ))) = ((card_ex κ).type)} : cast prf.symm p = (cast prf'.symm p.1, p.2) :=
-- begin
--   ext, swap, simp, h_generalize H_x : p == x, apply pi₂_cast₂, from eq₀, from H_x.symm,
--   h_generalize H_x : p == x, simp, h_generalize H_y : p.fst == y,
--   apply eq_of_heq, suffices : x.fst == p.fst, from heq.trans this H_y,
--   apply pi₂_cast₁, from eq₀, from H_x.symm
-- end

-- theorem cohen_algebra_CCC : CCC (cohen_algebra κ):=
-- by { apply CCC_regular_opens, apply cantor_space.countable_chain_condition_set }



-- local notation `𝒳` := set((card_ex κ).type × ℕ)

-- open topological_space



-- /-- The principal regular open associated to a pair (ν, n) is the collection of all subsets of
--     (card_ex κ) × ℕ which contain (ν, n). -/
-- variable (κ)
-- def principal_open (ν : ((card_ex κ)̌  : bSet (cohen_algebra κ)).type) (n : ℕ) : (cohen_algebra κ) :=
-- begin
--   use (cantor_space.principal_open (cast (eq₁) (ν, n))),
--   from is_regular_of_clopen (cantor_space.is_clopen_principal_open)
-- end

-- variable {κ}
-- lemma is_clopen_principal_open {ν n} : is_clopen (principal_open κ ν n).val :=
--   cantor_space.is_clopen_principal_open

-- local postfix `ᵖ`:80 := perp

-- local notation `cl`:65 := closure

-- local notation `int`:65 := interior

-- lemma perp_eq_compl_of_clopen {β : Type*} [topological_space β] {S : set β} (H : is_clopen S) : Sᵖ = (-S) :=
-- by {unfold perp, rw[closure_eq_of_is_closed H.right]}

-- lemma mem_neg_principal_open_of_not_mem {ν n S} : (cast (eq₁) (ν,n) ∈ (-S)) → S ∈ (- (principal_open κ ν n)).val :=
-- begin
--   intro H, simp only [neg_unfold], rw[perp_eq_compl_of_clopen],
--   swap, from is_clopen_principal_open, from H
-- end

-- variable (κ)
-- structure cohen_poset  : Type u :=
-- (ins : finset (((card_ex κ) ̌ : bSet (cohen_algebra κ)).type × ℕ))
-- (out : finset (((card_ex κ) ̌ : bSet (cohen_algebra κ)).type × ℕ))
-- (H : ins ∩ out = ∅)

-- variable{κ}

-- @[reducible]def π₂ : ((card_ex κ)̌  : bSet (cohen_algebra κ)).type × ℕ → ℕ := λ x, x.snd

-- -- def nat_supp : finset (((card_ex κ) ̌ : bSet (cohen_algebra κ)).type × ℕ) → set ℕ :=
-- -- λ X, {n | ∃ (ξ : (card_ex κ).type), (cast eq₁.symm (ξ,n)) ∈ X}

-- -- lemma nat_supp_finite {X} : set.finite $ nat_supp X := sorry

-- def cohen_poset_inc : cohen_poset κ → (cohen_algebra κ) :=
-- λ p, ⟨{S | (p.ins.to_set) ⊆ (cast (eq₂).symm S) ∧
--            (p.out.to_set) ⊆ (cast (eq₂).symm (- S))},
-- is_regular_of_clopen
--      begin
--        change is_clopen
--          ({S | p.ins.to_set ⊆ cast (eq₂).symm S} ∩ {S | p.out.to_set ⊆ (cast (eq₂).symm (-S))}),
--        refine is_clopen_inter _ _,
--          have := cantor_space.is_clopen_principal_open_finset p.ins,
--          convert this, from (eq₀).symm, from (eq₀).symm, from (eq₀).symm,
--            {apply function.hfunext, from (eq₂).symm, intros a a' H_heq,
--              apply heq_of_eq, convert rfl, convert (cast_eq _ _).symm, from (eq₀).symm, refl},

--          have := cantor_space.is_clopen_co_principal_open_finset p.out,
--          convert this, from (eq₀).symm, from (eq₀).symm, from (eq₀).symm,
--          {apply function.hfunext, from (eq₂).symm, intros a a' H_heq,
--           apply heq_of_eq, convert rfl, h_generalize Hx : (-a) == x,
--           have := heq.subst H_heq, swap,
--           from λ _ y, y == -x,
--           suffices : a' = -x, by {rw[this], simp},
--           apply eq_of_heq, apply this, apply compl_cast₂, from (eq₁).symm,
--           from Hx}
--      end⟩

-- open cantor_space

-- lemma prop_decidable_cast_lemma {α β : Type*} (H : α = β) {a b : α} {a' b' : β} (H_a : a == a') (H_b : b == b') : classical.prop_decidable (a = b) == classical.prop_decidable (a' = b') :=
-- by {subst H, subst H_a, subst H_b}

-- lemma cohen_poset_dense_basis : ∀ T ∈ @standard_basis ((card_ex κ).type × ℕ), ∀ h_nonempty : T ≠ ∅,
--   ∃ p : cohen_poset κ, (cohen_poset_inc p).val ⊆ T :=
-- begin
--   intros T Ht H_nonempty, simp[standard_basis] at Ht,
--   cases Ht with H_empty Ht, contradiction,
--   rcases Ht with ⟨p_ins, p_out, H₁, H₂⟩,
--   fsplit, refine ⟨_,_,_⟩, from cast eq₃.symm p_ins,
--   from cast eq₃.symm p_out, swap, rw[<-co_principal_open_finset_eq_inter] at H₁,
--   rw[<-principal_open_finset_eq_inter] at H₁, subst H₁,
--   intros S HS, split, cases HS, dsimp at HS_left, simp[principal_open_finset],
--   {convert HS_left,
--     from eq₀.symm, from eq₀.symm, from eq₀.symm, all_goals{symmetry, from cast_heq _ _}},
--   cases HS, dsimp at HS_right, simp[principal_open_finset],
--   {convert HS_right,
--     from eq₀.symm, from eq₀.symm, from eq₀.symm, all_goals{symmetry, from cast_heq _ _}},
--   convert H₂, from eq₀, from eq₀, from eq₀,
--   apply function.hfunext, from (eq₁), intros a a' H,
--   apply function.hfunext, from (eq₁), intros b b' H',
--   from prop_decidable_cast_lemma (eq₁) ‹_› ‹_›,
--   from cast_heq _ _, from cast_heq _ _, from eq₀, from eq₀
-- end

-- lemma cohen_poset_dense {b : (cohen_algebra κ)} (H : ⊥ < b) : ∃ p : cohen_poset κ, cohen_poset_inc p ≤ b :=
-- begin
--   cases (classical.choice (classical.nonempty_of_not_empty _ H.right.symm)) with S_wit H_wit,
--   change ∃ p, (cohen_poset_inc p).val ⊆ b.val,
--   have := mem_basis_subset_of_mem_open (is_topological_basis_standard_basis) H_wit (is_open_of_is_regular b.property),
--   rcases (mem_basis_subset_of_mem_open
--            (is_topological_basis_standard_basis) H_wit (is_open_of_is_regular b.property))
--          with ⟨v, Hv₁, Hv₂, Hv₃⟩,
--   have : v ≠ ∅, by {intro H, rw[H] at Hv₂, cases Hv₂},
--   cases (cohen_poset_dense_basis ‹_› ‹_› ‹_›) with p H_p, from ⟨p, set.subset.trans H_p ‹_›⟩
-- end

-- lemma to_set_inter {α : Type*} {p₁ p₂ : finset α} : (p₁ ∩ p₂).to_set = (p₁.to_set ∩ p₂.to_set) :=
-- by {ext, split; intros; unfold finset.to_set at *, tidy}

-- @[simp]lemma to_set_empty {α : Type*} : finset.to_set (∅ : finset α) = ∅ :=
-- by {unfold finset.to_set, refl}

-- lemma not_mem_of_inter_empty_left {α : Type*} {p₁ p₂ : finset α}
--   (H : p₁ ∩ p₂ = ∅) {a : α} : a ∈ p₁.to_set → ¬ a ∈ p₂.to_set :=
-- begin
--   intro H', intro H'',
--   have this₀ : a ∈ p₁.to_set ∩ p₂.to_set := ⟨‹_›,‹_›⟩,
--   rw[<-to_set_inter] at this₀, have this₁ := congr_arg finset.to_set H,
--   rw[this₁] at this₀, cases this₀
-- end

-- lemma not_mem_of_inter_empty_right {α : Type*} {p₁ p₂ : finset α}
--   (H : p₂ ∩ p₁ = ∅) {a : α} : a ∈ p₁.to_set → ¬ a ∈ p₂.to_set :=
-- by {rw[finset.inter_comm] at H, apply not_mem_of_inter_empty_left, from ‹_›}

-- lemma cohen_poset_nonzero (p : cohen_poset κ) : ⊥ ≠ (cohen_poset_inc p) :=
-- begin
--   intro H, replace H := H.symm, rw[eq_bot_iff] at H, rw[le_iff_subset''] at H,
--   rw[bot_eq_empty] at H,
--   suffices : nonempty (cohen_poset_inc p).val,
--     by {have := classical.choice this, specialize H this.property, cases H},
--   apply nonempty.intro, fsplit, exact (cast (eq₂) p.ins.to_set),
--   split, finish, intro x, cases x with ν n, intro H,
--   suffices : cast (eq₁) (ν, n) ∈ - cast (eq₂) (p.ins).to_set,
--     {convert this, from eq₀, from eq₀, from eq₀, cc, cc},
--   suffices : (ν, n) ∈ - p.ins.to_set,
--     {convert this, from eq₀.symm, from eq₀.symm, from eq₀.symm, cc, from eq₀.symm,
--      from eq₀.symm, from eq₀.symm, from eq₀.symm, cc},
--   from not_mem_of_inter_empty_right p.H H
-- end

-- lemma subset_of_eq {α : Type*} {a b : finset α} (H : a = b) : a ⊆ b := by rw[H]; refl

-- lemma cohen_poset_disjoint_row (p : cohen_poset κ) : ∃ n : ℕ, ∀ ξ : (card_ex κ).type, (cast (eq₁).symm (ξ,n)) ∉ p.ins ∧ (cast (eq₁).symm (ξ,n)) ∉ p.out :=
-- begin
--   let Y := (finset.image π₂ p.ins) ∪ (finset.image π₂ p.out),
--   by_cases (p.ins ∪ p.out) = ∅,
--   use 0, intro ξ, split, intro x, apply (subset_of_eq h), simp, left, from x,
--   intro x, apply (subset_of_eq h), simp, right, from x,
--   let Y' := finset.image π₂ (p.ins ∪ p.out),
--   have Y'_nonempty : Y' ≠ ∅,
--     by {dsimp[Y'], intro H, apply h, ext; split; intros, swap, cases a_1,
--       have : π₂ a ∈ finset.image π₂ (p.ins ∪ p.out), simp,
--       use a.fst, simp at a_1, convert a_1, cases a, refl, cases a, refl,
--       rw[H] at this, cases this},
--   have := finset.max_of_ne_empty,
--   specialize this Y'_nonempty, cases this with N HN, swap, apply_instance,
--   use (N+1), intro ξ, split,
--     intro X, let prf := _, change cast prf (ξ, N + 1) ∈ p.ins at X,
--     rw[eq₁_cast'] at X, swap, from eq₀,
--     have : N + 1 ∈ Y',
--       by {simp, use cast eq₀.symm ξ, from or.inl X},
--     suffices : N + 1 ≤ N, by {revert this, change ¬ (N + 1 ≤ N), apply nat.not_succ_le_self},
--     apply finset.le_max_of_mem this ‹_›,
--   intro X, let prf := _, change cast prf (ξ, N + 1) ∈ p.out at X,
--     rw[eq₁_cast'] at X, swap, from eq₀,
--     have : N + 1 ∈ Y',
--       by {simp, use cast eq₀.symm ξ, from or.inr X},
--     suffices : N + 1 ≤ N, by {revert this, change ¬ (N + 1 ≤ N), apply nat.not_succ_le_self},
--     apply finset.le_max_of_mem this ‹_›
-- end

-- lemma cohen_poset_anti {p₁ p₂ : cohen_poset κ} : p₁.ins ⊆ p₂.ins → p₁.out ⊆ p₂.out → cohen_poset_inc p₂ ≤ cohen_poset_inc p₁  :=
-- by {intros H₁ H₂, rw[le_iff_subset''], tidy}

-- end cohen_algebra
-- end cohen_algebra

-- namespace cohen_real

-- section cohen_real
-- variables (κ : cardinal.{u})
-- open cohen_algebra

-- -- attribute [instance, priority 0] 𝔹_boolean_algebra

-- -- variable [σ : nontrivial_complete_boolean_algebra 𝔹]

-- -- attribute [instance, priority 1000] σ
-- -- include σ
-- /-- `cohen_real.χ ν` is the indicator function on ℕ induced by every ordinal less than (card_ex κ) -/
-- def χ (ν : ((card_ex κ)̌  : bSet (cohen_algebra κ)).type) : ℕ → (cohen_algebra κ) :=
--   λ n, principal_open κ ν n

-- /-- `cohen_real.mk ν` is the subset of (ω : bSet (cohen_algebra κ)) induced by `cohen_real.χ ν` -/
-- def mk (ν : ((card_ex κ)̌  : bSet (cohen_algebra κ)).type) : bSet (cohen_algebra κ) :=
--   @set_of_indicator (cohen_algebra κ) _ omega $ λ n, χ κ ν n.down


-- variable {κ}
-- @[simp, cleanup]lemma mk_type {ν} : (mk κ ν).type = ulift ℕ := rfl

-- @[simp, cleanup]lemma mk_func {ν} {n} : (mk κ ν).func n = bSet.of_nat (n.down) := rfl

-- @[simp, cleanup]lemma mk_bval {ν} {n} : (mk κ ν).bval n = (χ κ ν) (n.down) := rfl

-- /-- bSet (cohen_algebra κ) believes that each `mk κ ν` is a subset of omega -/
-- lemma definite {ν} {Γ} : Γ ≤ mk κ ν ⊆ᴮ omega :=
-- by simp [mk, subset_unfold]; from λ _, by rw[<-deduction]; convert omega_definite

-- /-- bSet (cohen_algebra κ) believes that each `mk κ ν` is an element of 𝒫(ω) -/
-- lemma definite' {ν} {Γ} : Γ ≤ mk κ ν ∈ᴮ bv_powerset omega := bv_powerset_spec.mp definite

-- -- TODO(jesse) refactor this proof to use axiom of extensionality instead, or prove a more general version

-- lemma sep {n} {Γ} {ν₁ ν₂} (H₁ : Γ ≤ (of_nat n) ∈ᴮ (mk κ ν₁)) (H₂ : Γ ≤ (- ((of_nat n) ∈ᴮ (mk κ ν₂)))) :
--   Γ ≤ (- ((mk κ ν₁) =ᴮ (mk κ ν₂))) :=
-- begin
--   rw[bv_eq_unfold], rw[neg_inf, neg_infi, neg_infi], simp only [neg_imp],
--   refine le_sup_left_of_le _, rw[@bounded_exists (cohen_algebra κ) _ (mk κ ν₁) (λ z, -(z ∈ᴮ mk κ ν₂)) _],
--   swap, change B_ext _, simp[-imp_bot, imp_bot.symm],
--   apply bv_use (bSet.of_nat n), bv_split_goal
-- end

-- lemma not_mem_of_not_mem {p : cohen_poset κ} {ν} {n} (H : (ν,n) ∈ p.out) : cohen_poset_inc p ≤ -( (of_nat n) ∈ᴮ (mk κ ν)) :=
-- begin
-- rw[mem_unfold, neg_supr], bv_intro k, rw[neg_inf], simp,
--        by_cases n = k.down, swap, rw[bSet.of_nat_inj ‹_›],
--        from le_sup_right_of_le (by simp),
--        refine le_sup_left_of_le _, rw[<-h],
--        rw[le_iff_subset''], unfold cohen_poset_inc χ, rintros S ⟨H_S₁, H_S₂⟩,
--        apply mem_neg_principal_open_of_not_mem, have := H_S₂ H, convert this,
--        from eq₀.symm, from eq₀.symm, from eq₀.symm,
--        from cast_heq _ _, from (cast_heq _ _).symm
-- end

-- private lemma inj_cast_lemma (ν' : type ((card_ex κ)̌  : bSet (cohen_algebra κ))) (n' : ℕ) :
--   cast eq₁.symm (cast eq₀ ν', n') = (ν', n') :=
-- begin
--   let a := _, change cast a _ = _,
--   let b := _, change cast _ (cast b _, _) = _,
--   simp[b] at a, dedup, change cast a_1 _ = _, cc
-- end

-- /-- Whenever ν₁ ≠ ν₂ < (card_ex κ), bSet (cohen_algebra κ) believes that `mk κ ν₁` and `mk κ ν₂` are distinct -/
-- lemma inj {ν₁ ν₂} (H_neq : ν₁ ≠ ν₂) : (mk κ ν₁) =ᴮ (mk κ ν₂) ≤ (⊥ : (cohen_algebra κ)) :=
-- begin
--   by_contra, replace h := (bot_lt_iff_not_le_bot.mpr ‹_›),
--   cases cohen_poset_dense h with p H_p, cases cohen_poset_disjoint_row p with n H_n,
--   let p' : cohen_poset κ := { ins := insert (ν₁,n) (p.ins),
--   out := insert (ν₂,n) p.out,
--   H := by {ext, split; intro H, swap, cases H, have := p.H, simp at H, cases a_1 with ν' n',
--            cases H with H₁ H₂, specialize H_n (cast eq₀ ν'), cases H_n, cases H₁; cases H₂, cc,
--            exfalso, apply H_n_right, convert H₂, rw[show n = n', by cc], apply inj_cast_lemma,
--            exfalso, apply H_n_left, convert H₁, rw[show n = n', by cc], apply inj_cast_lemma,
--            rw[<-this], simp[*,-this]} },
--   have this₀ : cohen_poset_inc p' ≤ cohen_poset_inc p,
--     from cohen_poset_anti (by {dsimp[p'], from λ i _, by {simp, from or.inr ‹_›}})
--                 (by {dsimp[p'], from λ i _, by {simp, from or.inr ‹_›}}),
--   have this₁ : cohen_poset_inc p' ≤ (ñ̌) ∈ᴮ (mk κ ν₁),
--     by {rw[mem_unfold], apply bv_use (ulift.up n), refine le_inf _ bv_refl,
--          {simp [le_iff_subset'', χ, principal_open, cohen_poset_inc, cantor_space.principal_open],
--          have : (ν₁, n) ∈ p'.ins,
--            by simp[p'], intros S H_S _, specialize H_S this,
--               convert H_S; [from eq₀.symm, from eq₀.symm, from eq₀.symm, cc, cc]}},
--   have this₂ : cohen_poset_inc p' ≤ - ((ñ̌) ∈ᴮ (mk κ ν₂)),
--     by {have : (ν₂, n) ∈ p'.out, by {simp[p']},
--        from not_mem_of_not_mem ‹_›},
--   have this₃ : cohen_poset_inc p' ≤ - (mk κ ν₁ =ᴮ mk κ ν₂),
--     from sep ‹_› ‹_›,
--   have this₄ : cohen_poset_inc p' ≤ (mk κ ν₁ =ᴮ mk κ ν₂),
--     from le_trans this₀ ‹_›,
--   suffices : cohen_poset_inc p' = ⊥, from absurd this.symm (cohen_poset_nonzero p'),
--   bv_and_intro this₃ this₄, simpa using H
-- end
-- end cohen_real
-- end cohen_real

-- section neg_CH
-- variables (κ₁ κ₂ : cardinal.{u}) (H_reg₁ : is_regular κ₁) (H_reg₂ : is_regular κ₂) (H_inf₁ : cardinal.omega < κ₁) (H_inf₂ : cardinal.omega < κ₂) (H_lt : κ₁ < κ₂)

-- open cohen_algebra

-- local notation `ℵ₀` := (omega : bSet (cohen_algebra κ₂))

-- local notation `𝔠` := (bv_powerset ℵ₀)

-- local infix `≺`:75 := (λ x y, -(larger_than x y))

-- local infix `≼`:75 := (λ x y, injects_into x y)

-- lemma uncountable_fiber_of_regular' (κ₁ κ₂ : cardinal) (H_inf : cardinal.omega ≤ κ₁) (H_lt : κ₁ < κ₂) (H : cof (ord κ₂) = κ₂) (α : Type u) (H_α : #α = κ₁) (β : Type u) (H_β : #β = κ₂) (g : β → α)
--   : ∃ (ξ : α), cardinal.omega < #↥(g⁻¹' {ξ}) :=
-- begin
--   have := (@cardinal.exists_aleph κ₂).mp (le_of_lt (lt_of_le_of_lt ‹_› ‹_›)), cases this with k H_k, subst H_k,
--   have := (@cardinal.exists_aleph κ₁).mp ‹_›, cases this with k' H_k', subst H_k',
--   have := infinite_pigeonhole g _ _, cases this with ξ H_ξ, use ξ, rw[H_ξ],
--   all_goals{simp*}, from lt_of_le_of_lt ‹_› ‹_›
-- end

-- lemma uncountable_fiber_of_regular (κ₁ κ₂ : cardinal) (H_inf : cardinal.omega ≤ κ₁) (H_lt : κ₁ < κ₂) (H : cof (ord κ₂) = κ₂) (g : type (pSet.ordinal.mk (ord κ₂)  : pSet.{u}) → type (pSet.ordinal.mk (ord κ₁) : pSet.{u}))
--   : ∃ (ξ : type (pSet.ordinal.mk (ord κ₁))), cardinal.omega < #↥((λ (β : type (pSet.ordinal.mk (ord κ₂))), g β)⁻¹' {ξ}) :=
-- begin
--   have := (@exists_aleph κ₁).mp ‹_›, cases this with k₁ h, subst h,
--   have := (@exists_aleph κ₂).mp (le_of_lt (lt_of_le_of_lt ‹_› ‹_›)), cases this with k₂ h,
--   subst h,
--   from uncountable_fiber_of_regular' (aleph k₁) (aleph k₂) ‹_› ‹_› ‹_› _ (mk_type_mk_eq _ ‹_›) _ (mk_type_mk_eq _ (by simp*)) g
-- end

-- lemma cardinal_inequality_of_regular (κ₁ κ₂ : cardinal) (H_reg₁ : cardinal.is_regular κ₁) (H_reg₂ : cardinal.is_regular κ₂) (H_inf : (omega : cardinal) ≤ κ₁) (H_lt : κ₁ < κ₂) : (⊤ : (cohen_algebra κ₂)) ≤ (pSet.ordinal.mk (ord κ₁))̌  ≺ (pSet.ordinal.mk (ord κ₂))̌  :=
-- begin
--   simp[larger_than, -top_le_iff], rw[<-imp_bot],
--   bv_imp_intro, bv_cases_at'' H f, by_contra,
--   have := classical.axiom_of_choice
--             (AE_of_check_larger_than_check _ _ H_1 (bot_lt_iff_not_le_bot.mpr ‹_›)),
--   cases this with g g_spec,
--   suffices : ¬ CCC (cohen_algebra κ₂), from absurd cohen_algebra_CCC this,
--   apply not_CCC_of_uncountable_fiber; try{assumption},
--     {have := (@cardinal.exists_aleph κ₁).mp ‹_›, cases this with k' H_k', subst H_k', simp*},
--     {have := (@cardinal.exists_aleph κ₁).mp ‹_›, cases this with k' H_k', subst H_k', simp*,
--      have := (@exists_aleph κ₂).mp (le_of_lt (lt_of_le_of_lt ‹_› ‹_›)), cases this with k₂ h,
--      subst h, simp*},
--     {intros i₁ i₂ H_neq, from ordinal.mk_inj _ _ _ ‹_›},
--     {dsimp at g,
--      apply uncountable_fiber_of_regular' κ₁ κ₂; try{simp*},
--      from H_reg₂.right,
--      have := (@exists_aleph κ₂).mp (le_of_lt (lt_of_le_of_lt ‹_› ‹_›)), cases this with k₂ h,
--      subst h, from mk_type_mk_eq _ ‹_›, from mk_type_mk_eq _ (le_of_lt (lt_of_le_of_lt ‹_› ‹_›))}
-- end

-- lemma cohen_real.mk_ext : ∀ (i j : type ((card_ex κ₂)̌  : bSet (cohen_algebra κ₂))), func ((card_ex κ₂)̌ ) i =ᴮ func ((card_ex κ₂)̌ ) j ≤
--   (λ (x : type ((card_ex κ₂)̌ )), cohen_real.mk κ₂ x) i =ᴮ (λ (x : type ((card_ex κ₂)̌ )), cohen_real.mk κ₂ x) j :=
-- begin
--   intros i j, by_cases i = j,
--    {simp[h]},
--    {refine poset_yoneda _, intros Γ a, simp only [le_inf_iff] at *,
--      have : func ((card_ex κ₂)̌ ) i = ((card_ex κ₂).func (check_cast i))̌ ,
--        by simp[check_func],
--      rw[this] at a,
--      have : func ((card_ex κ₂)̌ ) j = ((card_ex κ₂).func (check_cast j))̌ ,
--        by simp[check_func],
--      rw[this] at a,
--    suffices : func (card_ex κ₂) (check_cast i)̌  =ᴮ func (card_ex κ₂) (check_cast j)̌  ≤ ⊥,
--      from le_trans a (le_trans this bot_le),
--    rw[le_bot_iff], apply check_bv_eq_bot_of_not_equiv,
--    apply ordinal.mk_inj, unfold check_cast, intro H, cc}
-- end



-- noncomputable def neg_CH_func : bSet (cohen_algebra κ₂) :=
-- @function.mk _ _ ((card_ex κ₂)̌ ) (λ x, cohen_real.mk κ₂ x) (cohen_real.mk_ext κ₂)

-- variables {κ₁ κ₂}
-- -- def CH : (cohen_algebra κ₂) := - ⨆ x, ⨆y, (ℵ₀ ≺ x) ⊓ (x ≺ y) ⊓ (y ≼ 𝒫(ℵ₀))

-- include κ₁ H_reg₁ H_inf₁

-- lemma ℵ₀_lt_κ₁ : (⊤ : (cohen_algebra κ₂))  ≤ ℵ₀ ≺ (card_ex κ₁)̌  :=
-- begin
--   simp[larger_than, -top_le_iff], rw[<-imp_bot],
--   bv_imp_intro, bv_cases_at'' H f, by_contra,
--   have := classical.axiom_of_choice
--             (AE_of_check_larger_than_check _ _ H_1 (bot_lt_iff_not_le_bot.mpr ‹_›)),
--   cases this with g g_spec,
--   suffices : ¬ CCC (cohen_algebra κ₂), from absurd cohen_algebra_CCC this,
--   apply not_CCC_of_uncountable_fiber; try{assumption},
--     {from le_of_eq (by simp)},
--     {simp*},
--     {intros i₁ i₂ H_neq, from ordinal.mk_inj _ _ _ ‹_›},
--     {dsimp at g,
--      apply uncountable_fiber_of_regular' (aleph 0) κ₁; try{simp*},
--      from H_reg₁.right}
-- end
-- omit H_reg₁ H_inf₁

-- theorem κ₂_le_𝔠 : (⊤ : cohen_algebra κ₂) ≤ is_func' ((card_ex κ₂)̌ ) 𝔠 (neg_CH_func κ₂) ⊓ is_inj (neg_CH_func κ₂) :=
-- begin
-- refine le_inf _ _,

--   {unfold neg_CH_func, refine le_inf _ _, refine mk_is_func _ _,
--     bv_intro w₁, bv_imp_intro, rw[mem_unfold] at H,
--     bv_cases_at'' H ν, apply bv_use (cohen_real.mk κ₂ ν),
--     refine le_inf cohen_real.definite' _, swap,
--     rw[mem_unfold], apply bv_use ν, bv_split,
--     from le_inf ‹_› (by apply le_trans H_1_right; from subst_congr_pair_left), refl},

--   {refine mk_inj_of_inj _ _, from λ _ _ _, cohen_real.inj ‹_›},
-- end

-- include H_reg₁ H_inf₁ H_reg₂ H_inf₂ H_lt

-- /-- For every pair of infinite regular cardinals κ₁ < κ₂, the continuum in bSet (cohen_algebra κ₂) is properly larger than (card_ex κ₁)̌ . -/
-- theorem neg_CH : (⊤ : cohen_algebra κ₂) ≤ -(CH) :=
-- begin
--   dsimp [CH], rw[lattice.neg_neg], apply bv_use ((card_ex κ₁)̌ ),
--   apply bv_use ((card_ex κ₂)̌ ), simp only [lattice.le_inf_iff],
--   refine ⟨⟨ℵ₀_lt_κ₁ H_reg₁ H_inf₁,_⟩,_⟩,
--   from  cardinal_inequality_of_regular _ _ (H_reg₁)
--   (H_reg₂) (le_of_lt ‹_›) (‹_›),
--   refine le_supr_of_le (neg_CH_func κ₂) _,
--   apply κ₂_le_𝔠, from κ₂
-- end



-- end neg_CH

