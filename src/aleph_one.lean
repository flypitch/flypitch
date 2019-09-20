import .bvm_extras2

universes u v

namespace pSet

section
open cardinal

lemma regularity (x : pSet.{u}) (H_nonempty : ¬ equiv x (∅ : pSet.{u})) : ∃ (y : pSet) (Hy : y ∈ x), ∀ z ∈ x, ¬ (z ∈ y) :=
begin
  have := is_epsilon_well_founded x,
  cases exists_mem_of_nonempty H_nonempty with w Hw,
  have := this x (subset_self) ‹_›,
    { rcases this with ⟨y, Hy₁, Hy₂⟩, exact ⟨y,‹_›,‹_›⟩ }
end

noncomputable def aleph_one : pSet := card_ex (aleph 1)

lemma aleph_one_Ord : Ord aleph_one := by apply Ord_mk

def aleph_one_weak_Ord_spec (x : pSet.{u}) : Prop :=
Ord x ∧ (∀ y : pSet.{u}, Ord y ∧ ¬ injects_into y pSet.omega → x ⊆ y)

def epsilon_trichotomy (x : pSet.{u}) : Prop := ∀ (y : pSet), y ∈ x → ∀ (z : pSet), z ∈ x → equiv y z ∨ y ∈ z ∨ z ∈ y

lemma epsilon_trichotomy_of_Ord {x : pSet.{u}} (H_ord : Ord x) : epsilon_trichotomy x :=
H_ord.left.left

lemma epsilon_trichotomy_of_Ord' {x : pSet.{u}} (H_ord : Ord x) : ∀ {y} (Hy : y ∈ x) {z} (Hz : z ∈ x), equiv y z ∨ y ∈ z ∨ z ∈ y :=
by { have :=  epsilon_trichotomy_of_Ord H_ord, intros, unfold epsilon_trichotomy at this, solve_by_elim }

lemma is_transitive_of_mem_Ord {x : pSet.{u}} (H_ord : Ord x) : is_transitive x := H_ord.right

lemma mem_of_mem_subset {x y z : pSet.{u}} (H_sub : y ⊆ z) (H_mem : x ∈ y) : x ∈ z :=
by {rw subset_iff_all_mem at H_sub, solve_by_elim}

lemma mem_of_mem_Ord {x y z : pSet.{u}} (H_ord : Ord z) (H_mem₁ : x ∈ y) (H_mem₂ : y ∈ z) : x ∈ z :=
begin
  have := is_transitive_of_mem_Ord H_ord,
  refine mem_of_mem_subset _ H_mem₁, solve_by_elim
end

lemma subset_of_mem_Ord {x z : pSet.{u}} (H_ord : Ord z) (H_mem₁ : x ∈ z) : x ⊆ z :=
by {cases H_ord with H_ewo H_trans, solve_by_elim}

lemma Ord_of_mem_Ord {x z : pSet.{u}} (H_mem : x ∈ z) (H : Ord z) : Ord x :=
begin
  refine ⟨_,_⟩,
    { refine ⟨_, by apply is_epsilon_well_founded⟩,
      intros y₁ Hy₁ y₂ Hy₂,
      apply (epsilon_trichotomy_of_Ord H); apply mem_of_mem_Ord; from ‹_› },
    { apply transitive_of_mem_Ord, repeat { assumption } }
end

def compl (x y : pSet.{u}) : pSet.{u} := {z ∈ x | ¬ z ∈ y}

lemma mem_compl_iff {x y z : pSet.{u}} : z ∈ compl x y ↔ z ∈ x ∧ ¬ z ∈ y :=
by {erw mem_sep_iff, simp}

@[reducible]def non_empty (x : pSet.{u}) : Prop := ¬ (equiv x (∅ : pSet.{u}))

lemma equiv_unfold' {x y : pSet.{u}} : equiv x y ↔ (∀ z, z ∈ x → z ∈ y) ∧ (∀ z, z ∈ y → z ∈ x ) :=
by simp [equiv.ext, subset_iff_all_mem]

lemma nonempty_iff_exists_mem {x : pSet.{u}} : non_empty x ↔ ∃ y, y ∈ x :=
begin
  refine ⟨_,_⟩,
    { exact exists_mem_of_nonempty },
    { intro H_ex_mem, intro H_eq, cases H_ex_mem with y Hy, apply pSet.mem_empty y, pSet_cc }
end

lemma nonempty_compl_of_ne {x y : pSet.{u}} (H_ne : ¬ equiv x y) : (non_empty $ compl x y) ∨ (non_empty $ compl y x) :=
begin
  rw equiv_unfold' at H_ne, push_neg at H_ne, cases H_ne,
    { rcases H_ne with ⟨z,Hz₁,Hz₂⟩, left, rw nonempty_iff_exists_mem, use z, simp[mem_compl_iff, *] },
    { rcases H_ne with ⟨z,Hz₁,Hz₂⟩, right, rw nonempty_iff_exists_mem, use z, simp [mem_compl_iff, *] }
end

lemma compl_empty_of_subset {x y : pSet.{u}} (H_sub : x ⊆ y) : equiv (compl x y) (∅ : pSet.{u}) :=
begin
  classical, by_contra H_contra, change non_empty _ at H_contra, rw nonempty_iff_exists_mem at H_contra,
  cases H_contra with z Hz, rw mem_compl_iff at Hz, cases Hz,
  suffices : z ∈ y,
    by contradiction,
  from mem_of_mem_subset H_sub ‹_›
end

def binary_inter (x y : pSet.{u}) : pSet.{u} := {z ∈ x | z ∈ y}

lemma mem_binary_inter_iff {x y z : pSet.{u}} : z ∈ binary_inter x y ↔ (z ∈ x ∧ z ∈ y) :=
by {erw mem_sep_iff, simp}

lemma binary_inter_subset {x y : pSet.{u}} : ((binary_inter x y ⊆ x) ∧ (binary_inter x y ⊆ y)) :=
by {refine ⟨_,_⟩; rw subset_iff_all_mem; intros z Hz; rw mem_binary_inter_iff at Hz; simp*}

lemma Ord_binary_inter {x y : pSet.{u}} (H₁ : Ord x) (H₂ : Ord y) : Ord (binary_inter x y) :=
begin
  refine ⟨⟨_,_⟩,_⟩,
    { intros w Hw_mem z Hz_mem, rw mem_binary_inter_iff at Hw_mem Hz_mem,
    have := epsilon_trichotomy_of_Ord H₁, tidy },
    { apply is_epsilon_well_founded },
    { intros z H_mem, rw mem_binary_inter_iff at H_mem, cases H_mem with H_mem₁ H_mem₂,
      rw subset_iff_all_mem, intros w Hw, rw mem_binary_inter_iff, refine ⟨_,_⟩,
        { exact mem_of_mem_Ord H₁ ‹_› ‹_› },
        { exact mem_of_mem_Ord H₂ ‹_› ‹_› }}
end

lemma Ord.lt_of_ne_and_le {x y : pSet.{u}} (H₁ :  Ord x) (H₂ :  Ord y) (H_ne : ¬ (equiv x y)) (H_le :  x ⊆ y) :  x ∈ y :=
begin
  have H_compl_nonempty : non_empty (compl y x),
    by { have this₁ := nonempty_compl_of_ne ‹_›,
         have this₂ := compl_empty_of_subset ‹_›,
         cases this₁,
           { exfalso, contradiction },
           { from ‹_› } },
  have H_ex_min := regularity _ H_compl_nonempty,
  rcases H_ex_min with ⟨z,⟨Hz₁,Hz₂⟩⟩,
  cases mem_compl_iff.mp Hz₁ with Hz₁ Hz₁',
  suffices H_eq : equiv x z, by pSet_cc,
  apply mem.ext, intro a, refine ⟨_,_⟩; intro H_mem,
    { have this' := epsilon_trichotomy_of_Ord' H₂ (mem_of_mem_subset H_le ‹_›) Hz₁,
      cases this',
        { exfalso, pSet_cc },
        { cases this',
          { from ‹_› },
          { exfalso, suffices : z ∈ x, by pSet_cc,
            refine mem_of_mem_Ord _ _ _, from a, repeat { assumption }}},},
    { classical, by_contra,
      have H_mem_y : a ∈ y,
        by {exact mem_of_mem_Ord ‹Ord y› H_mem ‹_› },
      have : a ∈ y ∧ ¬(a ∈ x) := ⟨‹_›,‹_›⟩,
      rw ←mem_compl_iff at this,
      refine absurd H_mem _, solve_by_elim }
end

lemma Ord.le_or_le {x y : pSet.{u}} (H₁ : Ord x) (H₂ : Ord y) : x ⊆ y ∨ y ⊆ x :=
begin
  let w := binary_inter x y,
  have w_Ord : Ord w := Ord_binary_inter H₁ H₂,
  have : equiv w x ∨ equiv w y,
    by { classical, by_contra H_contra, push_neg at H_contra,
         suffices : w ∈ x ∧ w ∈ y,
           by { suffices : w ∈ w, from mem_self ‹_›,
                rwa mem_binary_inter_iff },
         cases H_contra with H_contra₁ H_contra₂,
         refine ⟨_,_⟩,
           { exact Ord.lt_of_ne_and_le w_Ord ‹_› ‹_› binary_inter_subset.left },
           { exact Ord.lt_of_ne_and_le w_Ord H₂ ‹_› binary_inter_subset.right }},
  cases @binary_inter_subset x y with H_sub₁ H_sub₂, cases this,
    { left, dsimp[w] at this, pSet_cc },
    { right, dsimp[w] at this, pSet_cc }
end

lemma equiv.comm {x y : pSet.{u}} : equiv x y ↔ equiv y x :=
by {have := @equiv.symm, tidy} -- why does {[smt] eblast_using [equiv.symm]} fail here?

lemma Ord.trichotomy {x y : pSet.{u}} (H₁ : Ord x) (H₂ : Ord y) : equiv x y ∨ x ∈ y ∨ y ∈ x :=
begin
  classical, have := Ord.le_or_le H₁ H₂,
  cases this,
    { by_cases (equiv x y),
      { from or.inl ‹_› },
      { refine or.inr (or.inl _), from Ord.lt_of_ne_and_le H₁ H₂ ‹_› ‹_› }},
    { by_cases (equiv x y),
      { from or.inl ‹_› },
      { refine or.inr (or.inr _), rw equiv.comm at h,
        have := @Ord.lt_of_ne_and_le, tactic.back_chaining_using_hs },},
end

lemma Ord.lt_of_le_of_lt {x y z : pSet.{u}} (Hx : Ord x) (Hy : Ord y) (Hz : Ord z) (H_le : x ⊆ y) (H_lt : y ∈ z) : x ∈ z :=
begin
  have := Ord.trichotomy Hx Hy,
  have H_dichotomy : x ∈ y ∨ equiv x y,
    by {cases this, right, from ‹_›, cases this, left, from ‹_›,
        right, rw equiv.ext, refine ⟨‹_›,_⟩, apply Hx.right, from ‹_› },
  cases H_dichotomy,
    { apply mem_trans_of_transitive, from ‹_›, from ‹_›, from Hz.right },
    { rwa mem.congr_left (equiv.symm H_dichotomy) at H_lt }
end

lemma Ord.le_iff_lt_or_eq {x z : pSet.{u}} (H₁ : Ord x) (H₂ : Ord z) : x ⊆ z ↔ x ∈ z ∨ equiv x z :=
begin
  classical, refine ⟨_,_⟩; intro H,
    { by_cases H_eq : equiv x z,
      { right, from ‹_› },
      { left, refine Ord.lt_of_ne_and_le H₁ _ _ _, repeat { from ‹_› }}},
    { cases H,
      { from subset_of_mem_Ord H₂ ‹_› },
      { have : x ⊆ x := subset_self, pSet_cc }},
end

local prefix `#`:70 := cardinal.mk

lemma mk_injects_into_of_mk_le_omega {η : ordinal.{u}} (H_le : #(ordinal.mk η).type ≤ #(pSet.omega : pSet.{u}).type) : injects_into (ordinal.mk η) pSet.omega :=
begin
  have H_ex_inj : ∃ f : (ordinal.mk η).type → (omega : pSet.{u}).type, function.injective f,
    by exact cardinal.injection_of_mk_le ‹_›,
  cases H_ex_inj with f Hf,
  let ψ : (ordinal.mk η).type → pSet.{u} := λ i, omega.func (f i),
  have H_congr : ∀ i j, pSet.equiv ((ordinal.mk η).func i) ((ordinal.mk η).func j) → pSet.equiv (ψ i) (ψ j),
    by { intros i₁ i₂ H_eqv,
         suffices : i₁ = i₂, by subst this, classical, by_contra,
         have := ordinal.mk_inj η i₁ i₂ ‹_›, contradiction },
  have H_inj : ∀ i₁ i₂, equiv (ψ i₁) (ψ i₂) → equiv ((ordinal.mk η).func i₁) ((ordinal.mk η).func i₂),
    by {intros i₁ i₂ H_eqv,
        suffices : i₁ = i₂,
          by { subst this },
        have := omega_inj H_eqv, finish },
  use pSet.function.mk ψ H_congr,
  refine ⟨_,_⟩,
    { apply pSet.function.mk_is_func, simp* },
    { apply pSet.function.mk_inj_of_inj, from ‹_› }
end

lemma injects_into_omega_of_mem_aleph_one {z : pSet} (H_mem : z ∈ aleph_one) : injects_into z omega :=
begin
  rcases equiv_mk_of_mem_mk z H_mem with ⟨w, Hw_lt, Hz_eq⟩,
  suffices : injects_into (ordinal.mk w) omega,
    by { apply P_ext_injects_into_left, from equiv.symm ‹_›, from ‹_› },
  refine mk_injects_into_of_mk_le_omega _,
  rw [ordinal.mk_card, mk_omega_eq_mk_omega, ←cardinal.lt_succ],
  rwa [lt_ord, aleph_one_eq_succ_aleph_zero] at Hw_lt
end

lemma aleph_one_satisfies_spec : aleph_one_weak_Ord_spec aleph_one :=
begin
  refine ⟨aleph_one_Ord,_⟩,
  rintros z ⟨Hz₁, Hz₂⟩,
  rw Ord.le_iff_lt_or_eq (aleph_one_Ord) ‹_›,
  have := Ord.trichotomy aleph_one_Ord ‹_›,
  cases this with this₁ this,
    { from or.inr ‹_› },
    { cases this with this₂ this₃,
      { from or.inl ‹_› },
      { exfalso, from absurd (injects_into_omega_of_mem_aleph_one ‹_›) ‹_› }}
end

end

end pSet
open lattice bSet cardinal
namespace bSet


local notation `ℵ₁` := pSet.aleph_one

local infix ` ⟹ `:65 := lattice.imp

local infix ` ⇔ `:50 := lattice.biimp

local infix `≺`:75 := (λ x y, -(larger_than x y))

local infix `≼`:75 := (λ x y, injects_into x y)

section well_ordering

variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

@[reducible]def is_rel (r x : bSet 𝔹) : 𝔹 := r ⊆ᴮ prod x x

def is_wo (r x : bSet 𝔹) : 𝔹 :=
is_rel r x ⊓ ((⨅y, pair y x ∈ᴮ r ⟹ (⨅z, pair z x ∈ᴮ r ⟹ (y =ᴮ z ⊔ pair y z ∈ᴮ r ⊔ pair z y ∈ᴮ r))) ⊓
  (⨅u, u ⊆ᴮ x ⟹ (- (u =ᴮ ∅) ⟹ ⨆y, pair y u ∈ᴮ r ⊓ (⨅z', pair z' u ∈ᴮ r ⟹ (- (pair z' y ∈ᴮ r))))))

def mem_rel (x : bSet 𝔹) : bSet 𝔹 := subset.mk (λ pr : (prod x x).type, x.func pr.1 ∈ᴮ x.func pr.2)

lemma mem_mem_rel_iff {x y z: bSet 𝔹} {Γ} : Γ ≤ pair y z ∈ᴮ mem_rel x ↔ (Γ ≤ y ∈ᴮ x ∧ Γ ≤ z ∈ᴮ x ∧ Γ ≤ y ∈ᴮ z) :=
begin
  erw mem_subset.mk_iff, refine ⟨_,_⟩; intro H,
    { simp at H, simp only [le_inf_iff.symm], bv_cases_at H pr Hpr,
      bv_split_at Hpr, rw pair_eq_pair_iff at Hpr_left, cases Hpr_left with H₁ H₂,
      simp only [le_inf_iff] at ⊢ Hpr_right, rcases Hpr_right with ⟨H'₁,H'₂,H'₃⟩,
      refine ⟨_,_,_⟩,
        { apply bv_rw' H₁, simp, simp* },
        { apply bv_rw' H₂, simp, simp* },
        { apply bv_rw' H₁, simp, apply bv_rw' H₂, simpa }},
    { rcases H with ⟨H₁, H₂, H₃⟩,
      have H₄ := H₁, have H₅ := H₂, rw mem_unfold at H₄ H₅,
      bv_cases_at H₄ i Hi, bv_cases_at H₅ j Hj, bv_split_at Hi, bv_split_at Hj,
      apply bv_use (i,j), refine le_inf _ _,
        { dsimp, rw pair_eq_pair_iff, from ⟨‹_›, ‹_›⟩ },
        { tidy, bv_cc } }
end

@[simp]lemma B_congr_mem_rel : B_congr (mem_rel : bSet 𝔹 → bSet 𝔹) :=
begin
  intros x y Γ H_eq, apply prod_ext, apply subset.mk_subset,
  { suffices : Γ ≤ prod x x =ᴮ prod y y, by {apply bv_rw' this, simp, apply subset.mk_subset },
    exact prod_congr H_eq H_eq },
  { bv_intro v, bv_imp_intro Hv_mem, bv_intro w, bv_imp_intro Hw_mem,
    refine le_inf _ _,
      { bv_imp_intro Hpr_mem, erw mem_mem_rel_iff at Hpr_mem ⊢, tidy; bv_cc },
      { bv_imp_intro Hpr_mem, erw mem_mem_rel_iff at Hpr_mem ⊢, tidy; bv_cc },}
end

def prod.map (x y v w : bSet 𝔹) (f g : bSet 𝔹) : bSet 𝔹 := subset.mk (λ (pr : (prod (prod x v) (prod y w)).type), pair (x.func pr.1.1) (y.func pr.2.1) ∈ᴮ f ⊓ pair (v.func pr.1.2) (w.func pr.2.2) ∈ᴮ g)

def prod.map_self (x y f : bSet 𝔹) : bSet 𝔹 :=
prod.map x y x y f f

lemma B_congr_prod.map_self_left_aux {y f x x' : bSet 𝔹} {Γ : 𝔹} {H_eq : Γ ≤ x =ᴮ x'}
: Γ ≤
    ⨅ (z : bSet 𝔹),
      z ∈ᴮ (λ (x : bSet 𝔹), prod.map_self x y f) x ⟹ z ∈ᴮ (λ (x : bSet 𝔹), prod.map_self x y f) x' :=
begin
   bv_intro z, bv_imp_intro H_mem, erw mem_subset.mk_iff₂ at H_mem ⊢,
      bv_cases_at H_mem pr Hpr,
      cases pr with pr₁ pr₂, cases pr₁ with a₁ a₂, cases pr₂ with b₁ b₂,
      dsimp only at Hpr,
      bv_split_at Hpr, bv_split_at Hpr_right, bv_split_at Hpr_right_right,
      simp at Hpr_left, rcases Hpr_left with ⟨⟨Ha₁, Ha₂⟩, Hb₁, Hb₂⟩,
      have Ha₁_mem : Γ_2 ≤ (x.func a₁) ∈ᴮ x' := bv_rw'' H_eq (mem.mk'' ‹_›),
      have Ha₂_mem : Γ_2 ≤ (x.func a₂) ∈ᴮ x' := bv_rw'' H_eq (mem.mk'' ‹_›),
      rw mem_unfold at Ha₁_mem Ha₂_mem, bv_cases_at Ha₁_mem a₁' Ha₁',

      bv_cases_at Ha₂_mem a₂' Ha₂', apply bv_use ((a₁', a₂'), (b₁, b₂)),
      bv_split_at Ha₁', bv_split_at Ha₂',
      refine le_inf (le_inf (le_inf ‹_› ‹_›) (le_inf ‹_› ‹_›) ) (le_inf _ (le_inf _ _)),
        { apply bv_rw' Hpr_right_left, simp, erw pair_eq_pair_iff, refine ⟨_,_⟩,
          { erw pair_eq_pair_iff, from ⟨‹_›,‹_›⟩ },
          { erw pair_eq_pair_iff, from ⟨bv_refl, bv_refl⟩ } },
        { dsimp, change _ ≤ (λ w, pair w (func y b₁) ∈ᴮ f) _, apply bv_rw' (bv_symm Ha₁'_right),
          from B_ext_pair_mem_left, from ‹_› },
        { dsimp, change _ ≤ (λ w, pair w (func y b₂) ∈ᴮ f) _, apply bv_rw' (bv_symm Ha₂'_right),
          from B_ext_pair_mem_left, from ‹_› }
end

@[simp]lemma B_congr_prod.map_self_left { y f : bSet 𝔹 } : B_congr (λ x : bSet 𝔹, prod.map_self x y f ) :=
begin
  intros x x' Γ H_eq, refine mem_ext _ _,
    { apply B_congr_prod.map_self_left_aux, from ‹_› },
    { apply B_congr_prod.map_self_left_aux, from bv_symm ‹_› }
end

lemma mem_prod.map_self_iff { x y f a₁ a₂ b₁ b₂ : bSet 𝔹 } { Γ : 𝔹 } (H_func : Γ ≤ is_function x y f) :
  Γ ≤ pair (pair a₁ a₂) (pair b₁ b₂) ∈ᴮ prod.map_self x y f ↔ Γ ≤ a₁ ∈ᴮ x ∧ Γ ≤ a₂ ∈ᴮ x ∧ Γ ≤ b₁ ∈ᴮ y ∧ Γ ≤ b₂ ∈ᴮ y ∧ Γ ≤ pair a₁ b₁ ∈ᴮ f ∧ Γ ≤ pair a₂ b₂ ∈ᴮ f :=
begin
  refine ⟨_,_⟩; intro H,
    { erw mem_subset.mk_iff₂ at H, simp only [le_inf_iff.symm],
      bv_cases_at H pr Hpr, rcases pr with ⟨⟨i₁,i₂⟩, ⟨j₁,j₂⟩⟩,
      simp only [le_inf_iff] at Hpr, rcases Hpr with ⟨Hpr, Hpr', Hpr'', Hpr'''⟩,
      simp only [le_inf_iff], simp at Hpr, rcases Hpr with ⟨⟨Hi₁, Hi₂⟩, Hj₁, Hj₂⟩,
      have Ha₁_mem : Γ_1 ≤ (x.func i₁) ∈ᴮ x := (mem.mk'' ‹_›),
      have Ha₂_mem : Γ_1 ≤ (x.func i₂) ∈ᴮ x := (mem.mk'' ‹_›),
      have Hb₁_mem : Γ_1 ≤ (y.func j₁) ∈ᴮ y := (mem.mk'' ‹_›),
      have Hb₂_mem : Γ_1 ≤ (y.func j₂) ∈ᴮ y := (mem.mk'' ‹_›),
      repeat {erw pair_eq_pair_iff at Hpr'},
      dsimp at Hpr', rcases Hpr' with ⟨⟨Heq₁, Heq₂⟩, Heq₃, Heq₄⟩,
      refine ⟨_,_,_,_,_,_⟩,
        { bv_cc },
        { bv_cc },
        { bv_cc },
        { bv_cc },
        { suffices : Γ_1 ≤ pair a₁ b₁ =ᴮ pair (func x i₁) (func y j₁),
            by { change _ ≤ (λ w, w ∈ᴮ f) _, apply bv_rw' (this), simp, from ‹_› },
          rw pair_eq_pair_iff, exact ⟨‹_›,‹_›⟩ },
        { suffices : Γ_1 ≤ pair a₂ b₂ =ᴮ pair (func x i₂) (func y j₂),
            by { change _ ≤ (λ w, w ∈ᴮ f) _, apply bv_rw' (this), simp, from ‹_› },
          rw pair_eq_pair_iff, exact ⟨‹_›,‹_›⟩ }},
    { rcases H with ⟨Ha₁_mem, Ha₂_mem, Hb₁_mem, Hb₂_mem, Hpr₁_mem, Hpr₂_mem⟩,
      erw mem_subset.mk_iff₂,
      rw mem_unfold at Ha₁_mem Ha₂_mem Hb₁_mem Hb₂_mem,
      bv_cases_at Ha₁_mem i₁ Hi₁, bv_split_at Hi₁,
      bv_cases_at Ha₂_mem i₂ Hi₂, bv_split_at Hi₂,
      bv_cases_at Hb₁_mem j₁ Hj₁, bv_split_at Hj₁,
      bv_cases_at Hb₂_mem j₂ Hj₂, bv_split_at Hj₂,
      apply bv_use ((i₁,i₂), (j₁,j₂)),
      refine le_inf (le_inf (le_inf ‹_› ‹_›) (le_inf ‹_› ‹_›)) (le_inf _ (le_inf _ _)),
        { repeat {erw pair_eq_pair_iff}, simp* },
        { dsimp, suffices : Γ_4 ≤ pair (func x i₁) (func y j₁) =ᴮ pair a₁ b₁,
            by { change _ ≤ (λ w, w ∈ᴮ f) _, apply bv_rw' this, simp, from ‹_› },
          rw pair_eq_pair_iff, refine ⟨bv_symm _, bv_symm _⟩; assumption },
        { dsimp, suffices : Γ_4 ≤ pair (func x i₂) (func y j₂) =ᴮ pair a₂ b₂,
            by { change _ ≤ (λ w, w ∈ᴮ f) _, apply bv_rw' this, simp, from ‹_› },
          rw pair_eq_pair_iff, refine ⟨bv_symm _, bv_symm _⟩; assumption } }
end

def induced_epsilon_rel (η : bSet 𝔹) (x : bSet 𝔹) (f : bSet 𝔹) : bSet 𝔹 :=
image (mem_rel η) (prod x x) (prod.map_self η x f)

lemma eq_pair_of_mem_induced_epsilon_rel {η x f pr : bSet 𝔹} {Γ} (H_mem : Γ ≤ pr ∈ᴮ induced_epsilon_rel η x f) : ∃ a b : bSet 𝔹, Γ ≤ a ∈ᴮ x ∧ Γ ≤ b ∈ᴮ x ∧ Γ ≤ pr =ᴮ pair a b ∧ Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f :=
begin
  have : Γ ≤ pr ∈ᴮ prod x x,
    by {refine mem_of_mem_subset _ H_mem, apply subset.mk_subset},
  rw mem_prod_iff₂ at this, rcases this with ⟨v,Hv,w,Hw,H_eq⟩,
  use v, use w, refine ⟨‹_›,‹_›,‹_›, _⟩,
  change _ ≤ (λ z, z ∈ᴮ induced_epsilon_rel η x f) _, apply bv_rw' (bv_symm H_eq), simpa
end

lemma mem_induced_epsilon_rel_iff { η x f a b : bSet 𝔹 } { Γ } (H_func : Γ ≤ is_function η x f) : Γ ≤ pair a b ∈ᴮ (induced_epsilon_rel η x f) ↔ (Γ ≤ a ∈ᴮ x) ∧ (Γ ≤ b ∈ᴮ x) ∧ (Γ ≤ ⨆ a', a' ∈ᴮ η ⊓ ⨆ b', b' ∈ᴮ η ⊓ (pair a' a ∈ᴮ f ⊓ pair b' b ∈ᴮ f ⊓ a' ∈ᴮ b')) :=
begin
  refine ⟨_,_⟩; intro H,
  { erw mem_image_iff at H, cases H with H₁ H₂,
     simp at H₁, cases H₁ with H₁ H₁',
      refine ⟨‹_›,‹_›,_⟩,
      bv_cases_at H₂ z Hz, bv_split_at Hz,
      have : Γ_1 ≤ z ∈ᴮ prod η η,
        by {refine mem_of_mem_subset _ Hz_left, apply subset.mk_subset },
      rw mem_prod_iff₂ at this, rcases this with ⟨v,Hv,w,Hw,H_eq⟩,
     apply bv_use v, refine le_inf ‹_› (bv_use w), refine le_inf ‹_› _,
     have : Γ_1 ≤ pair (pair v w) (pair a b) ∈ᴮ prod.map_self η x f,
       by { change _ ≤ (λ k, pair k (pair a b) ∈ᴮ prod.map_self η x f) _, apply bv_rw' (bv_symm H_eq),
            simp, from ‹_› },
     rw mem_prod.map_self_iff at this, rcases this with ⟨_,_,_,_,_,_⟩,
     refine le_inf (le_inf ‹_› ‹_›) _,
     suffices : Γ_1 ≤ (pair v w ∈ᴮ mem_rel η),
       by { rw mem_mem_rel_iff at this, simp* },
     change _ ≤ (λ s, s ∈ᴮ mem_rel η) _, apply bv_rw' (bv_symm H_eq), simp, from ‹_›, from ‹_› },
    { rcases H with ⟨H₁,H₂,H₃⟩, bv_cases_at H₃ a' Ha',
      bv_split_at Ha', bv_cases_at Ha'_right b' Hb',
      bv_split_at Hb',
      erw mem_image_iff,
      refine ⟨_,_⟩,
        { rw mem_prod_iff, bv_split_at Hb'_right, bv_split_at Hb'_right_left,
          refine ⟨_,_⟩,
            { apply mem_codomain_of_is_function ‹_› ‹_› },
            { apply mem_codomain_of_is_function ‹Γ_2 ≤ pair b' b ∈ᴮ f› ‹_› }},
        { apply bv_use (pair a' b'), refine le_inf _ _,
          { rw mem_mem_rel_iff, exact ⟨‹_›,‹_›,bv_and.right ‹_›⟩ },
          { rw mem_prod.map_self_iff, refine ⟨‹_›,‹_›, ‹_›, ‹_›, _⟩, bv_split_at Hb'_right,
            bv_split_at Hb'_right_left, from ⟨‹_›,‹_›⟩, from ‹_› }}}
end

lemma mem_induced_epsilon_rel_of_mem {η x f a b : bSet 𝔹} {Γ} (H_mem₁ : Γ ≤ a ∈ᴮ η) (H_mem₂ : Γ ≤ b ∈ᴮ η) (H_mem : Γ ≤ a ∈ᴮ b) (H_func : Γ ≤ is_function η x f) : Γ ≤ pair (function_eval H_func a H_mem₁) (function_eval H_func b H_mem₂) ∈ᴮ induced_epsilon_rel η x f :=
begin
  rw mem_induced_epsilon_rel_iff ‹_›,
  refine ⟨_,_,_⟩,
    { apply function_eval_mem_codomain },
    { apply function_eval_mem_codomain },
    { apply bv_use a, refine le_inf ‹_› (bv_use b),
      refine le_inf ‹_› (le_inf (le_inf _ _) ‹_›),
        { apply function_eval_pair_mem },
        { apply function_eval_pair_mem }}
end

lemma mem_of_mem_induced_epsilon_rel {η x f a' b' a b : bSet 𝔹} {Γ} (H_inj : Γ ≤ is_injective_function η x f) (H_mem₁ : Γ ≤ pair a' a ∈ᴮ f) (H_mem₂ : Γ ≤ pair b' b ∈ᴮ f) (H_mem : Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f) : Γ ≤ a' ∈ᴮ b' :=
begin
  rw (mem_induced_epsilon_rel_iff $ bv_and.left ‹_›) at H_mem,
  rcases H_mem with ⟨Ha_mem, Hb_mem, H⟩,
  bv_cases_at H a'' Ha'', bv_split_at Ha'', bv_cases_at Ha''_right b'' Hb'', simp only [le_inf_iff] at Hb'',
  rcases Hb'' with ⟨Hb''₁, ⟨Hb''₂, Hb''₃⟩, Hb''₄⟩,
  suffices : Γ_2 ≤ a' =ᴮ a'' ∧ Γ_2 ≤ b' =ᴮ b'',
    by {cases this, bv_cc},
  have H_inj' := is_inj_of_is_injective_function H_inj,
  refine ⟨_,_⟩,
    { refine H_inj' a' a'' a a _, exact le_inf (le_inf ‹_› ‹_›) bv_refl },
    { refine H_inj' b' b'' b b _, exact le_inf (le_inf ‹_› ‹_›) bv_refl }
end

lemma induced_epsilon_rel_sub_image_left { η x f a b : bSet 𝔹 } { Γ } (H_func : Γ ≤ is_function η x f) (H : Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f ) : Γ ≤ a ∈ᴮ image η x f :=
begin
  rw mem_image_iff, rw mem_induced_epsilon_rel_iff at H,
  rcases H with ⟨H₁,H₂,H₃⟩, refine ⟨‹_›, _⟩,
  bv_cases_at H₃ a' Ha', bv_split_at Ha', bv_cases_at Ha'_right b' Hb',
  bv_split_at Hb', bv_split_at Hb'_right, bv_split_at Hb'_right_left,
  apply bv_use a', from le_inf ‹_› ‹_›,
  from ‹_›
end

lemma induced_epsilon_rel_sub_image_right { η x f a b : bSet 𝔹 } { Γ } (H_func : Γ ≤ is_function η x f) (H : Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f ) : Γ ≤ b ∈ᴮ image η x f :=
begin
  rw mem_image_iff, rw mem_induced_epsilon_rel_iff at H,
  rcases H with ⟨H₁,H₂,H₃⟩, refine ⟨‹_›, _⟩,
  bv_cases_at H₃ a' Ha', bv_split_at Ha', bv_cases_at Ha'_right b' Hb',
  bv_split_at Hb', bv_split_at Hb'_right, bv_split_at Hb'_right_left,
  apply bv_use b', from le_inf ‹_› ‹_›,
  from ‹_›
end

lemma image_eq_of_eq_induced_epsilon_rel_aux
  { η ρ f g : bSet 𝔹 }
  { Γ }
  (Hη_inj : Γ ≤ is_injective_function η omega f)
  (Hρ_inj : Γ ≤ is_injective_function ρ omega g)
  (H_eq : Γ ≤ induced_epsilon_rel η omega f =ᴮ induced_epsilon_rel ρ omega g)
  (H_exists_two : Γ ≤ exists_two η) :
  Γ ≤ ⨅ (z : bSet 𝔹), z ∈ᴮ image η omega f ⟹ z ∈ᴮ image ρ omega g :=
begin
bv_intro z, bv_imp_intro Hz_mem, rw mem_image_iff at Hz_mem,
     cases Hz_mem with Hz_mem₁ Hz_mem₂,
     bv_cases_at Hz_mem₂ z' Hz', bv_split_at Hz',
     unfold exists_two at H_exists_two,
     replace H_exists_two := H_exists_two z' ‹_›,
     bv_cases_at H_exists_two w' Hw', bv_split_at Hw',
     bv_or_elim_at' Hw'_right,
       { let w := function_eval (bv_and.left Hη_inj) w' ‹_›,
         apply induced_epsilon_rel_sub_image_left, show bSet 𝔹, from w, from bv_and.left ‹_›,
         apply bv_rw' (bv_symm H_eq), { simp },
         rw mem_induced_epsilon_rel_iff,
         refine ⟨‹_›, by { apply function_eval_mem_codomain }, _⟩, apply bv_use z',
         refine le_inf ‹_› _, apply bv_use w', refine le_inf ‹_› _,
         refine le_inf (le_inf ‹_› (by apply function_eval_pair_mem)) ‹_›, from bv_and.left ‹_› },
       { let w := function_eval (bv_and.left Hη_inj) w' ‹_›,
         apply induced_epsilon_rel_sub_image_right, show bSet 𝔹, from w, from bv_and.left ‹_›,
         apply bv_rw' (bv_symm H_eq), { simp },
         rw mem_induced_epsilon_rel_iff,
         refine ⟨ by { apply function_eval_mem_codomain }, ‹_›, _⟩, apply bv_use w',
         refine le_inf ‹_› _, apply bv_use z', refine le_inf ‹_› _,
         refine le_inf (le_inf (by apply function_eval_pair_mem) ‹_›) ‹_›, from bv_and.left ‹_› }
end

lemma image_eq_of_eq_induced_epsilon_rel
  { η ρ f g : bSet 𝔹 }
  { Γ }
  (Hη_inj : Γ ≤ is_injective_function η omega f)
  (Hρ_inj : Γ ≤ is_injective_function ρ omega g)
  (H_eq : Γ ≤ induced_epsilon_rel η omega f =ᴮ induced_epsilon_rel ρ omega g)
  (H_exists_two : Γ ≤ exists_two η)
  (H_exists_two' : Γ ≤ exists_two ρ) :
  Γ ≤ image η omega f =ᴮ image ρ omega g :=
by { refine mem_ext _ _;
     apply image_eq_of_eq_induced_epsilon_rel_aux; repeat { assumption }, from bv_symm ‹_› }

lemma eq_of_eq_induced_epsilon_rel
  {η ρ f g : bSet 𝔹}
  {Γ}
  (Hη_ord : Γ ≤ Ord η)
  (Hρ_ord : Γ ≤ Ord ρ)
  (Hη_inj : Γ ≤ is_injective_function η omega f)
  (Hρ_inj : Γ ≤ is_injective_function ρ omega g)
  (H_eq : Γ ≤ induced_epsilon_rel η omega f =ᴮ induced_epsilon_rel ρ omega g)
  (H_exists_two : Γ ≤ exists_two η)
  (H_exists_two' : Γ ≤ exists_two ρ)
  : Γ ≤ η =ᴮ ρ :=
begin
  suffices : Γ ≤ ⨆ h, eps_iso η ρ h,
    by { exact eq_of_Ord_eps_iso Hη_ord Hρ_ord ‹_› },
  refine bv_use (injective_function_comp (factor_image_is_injective_function Hη_inj) _),
  from ρ, from injective_function_inverse Hρ_inj,
  { apply @bv_rw' _ _ _ _ _ (image_eq_of_eq_induced_epsilon_rel Hη_inj Hρ_inj ‹_› ‹_› ‹_›) (λ z, is_injective_function z ρ (injective_function_inverse Hρ_inj)), simp, from injective_function_inverse_is_injective_function },
  refine le_inf (le_inf _ _) _,
    { apply injective_function_comp_is_function },
    { rw strong_eps_hom_iff, intros,
      apply_all le_trans H_le, refine ⟨_,_⟩; intro H_mem,
        { erw mem_is_func'_comp_iff at Hpr₁_mem, rcases Hpr₁_mem with ⟨_,_,Hv₁_ex⟩,
          erw mem_is_func'_comp_iff at Hpr₂_mem, rcases Hpr₂_mem with ⟨_,_,Hv₂_ex⟩,
          bv_cases_at Hv₁_ex v₁ Hv₁, bv_cases_at Hv₂_ex v₂ Hv₂,
          have v₁_mem_v₂ : Γ_2 ≤ pair v₁ v₂ ∈ᴮ induced_epsilon_rel η omega f,
            by { rw mem_induced_epsilon_rel_iff, refine ⟨_,_,_⟩,
                 { refine mem_of_mem_subset _ (bv_and.left Hv₁), apply image_subset },
                 { refine mem_of_mem_subset _ (bv_and.left Hv₂), apply image_subset },
                 { apply bv_use z₁, refine le_inf ‹_› (bv_use z₂),
                   refine le_inf ‹_› (le_inf (le_inf _ _) _),
                     { bv_split, bv_split, from ‹_› },
                     { bv_split, bv_split, from ‹_› },
                     { from ‹_› } }, from bv_and.left ‹_› },
          have Hpr₁_mem : Γ_2 ≤ pair w₁ v₁ ∈ᴮ g,
            by { bv_split_at Hv₁, bv_split_at Hv₁_right, erw mem_inj_inverse_iff at Hv₁_right_right, simp* },
          have Hpr₂_mem : Γ_2 ≤ pair w₂ v₂ ∈ᴮ g,
            by { bv_split_at Hv₂, bv_split_at Hv₂_right, erw mem_inj_inverse_iff at Hv₂_right_right, simp* },
          refine mem_of_mem_induced_epsilon_rel Hρ_inj_1 Hpr₁_mem Hpr₂_mem _,
          apply bv_rw' (bv_symm H_eq_1), simp, from ‹_› },
        { erw mem_is_func'_comp_iff at Hpr₁_mem, rcases Hpr₁_mem with ⟨_,_,Hv₁_ex⟩,
          erw mem_is_func'_comp_iff at Hpr₂_mem, rcases Hpr₂_mem with ⟨_,_,Hv₂_ex⟩,
          bv_cases_at Hv₁_ex v₁ Hv₁, bv_cases_at Hv₂_ex v₂ Hv₂,
          have v₁_mem_v₂ : Γ_2 ≤ pair v₁ v₂ ∈ᴮ induced_epsilon_rel ρ omega g,
            by { rw mem_induced_epsilon_rel_iff, refine ⟨_,_,_⟩,
                 { refine mem_of_mem_subset _ (bv_and.left Hv₁), apply image_subset },
                 { refine mem_of_mem_subset _ (bv_and.left Hv₂), apply image_subset },
                 { apply bv_use w₁, refine le_inf ‹_› (bv_use w₂),
                   refine le_inf ‹_› (le_inf (le_inf _ _) _),
                     { bv_split_at Hv₁, bv_split_at Hv₁_right, erw mem_inj_inverse_iff at Hv₁_right_right, simp* },
                     { bv_split_at Hv₂, bv_split_at Hv₂_right, erw mem_inj_inverse_iff at Hv₂_right_right, simp* },
                     { from ‹_› } }, from bv_and.left ‹_› },
          have Hpr₁_mem : Γ_2 ≤ pair z₁ v₁ ∈ᴮ f,
            by bv_split; bv_split; from ‹_›,
          have Hpr₂_mem : Γ_2 ≤ pair z₂ v₂ ∈ᴮ f,
            by bv_split; bv_split; from ‹_›,
          refine mem_of_mem_induced_epsilon_rel Hη_inj_1 Hpr₁_mem Hpr₂_mem _,
          apply bv_rw' H_eq_1, simp, from ‹_› },
         },
    {apply is_func'_comp_surj,
       { from bv_and.right ‹_› },
       { apply injective_function_inverse_is_inj },
       { exact surj_image (is_func'_of_is_injective_function Hη_inj) },
       { change _ ≤ (λ z, is_surj z ρ (injective_function_inverse Hρ_inj)) _,
         apply bv_rw' (image_eq_of_eq_induced_epsilon_rel Hη_inj Hρ_inj ‹_› ‹_› ‹_›), simp, apply inj_inverse.is_surj }}
end

end well_ordering

section a1
parameters {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

def a1.ϕ : bSet 𝔹 → 𝔹 := λ x, (⨆η, Ord η ⊓ ⨆ f, is_injective_function η omega f ⊓ (image (mem_rel η) (prod omega omega) (prod.map_self η omega f) =ᴮ x) ⊓ (- (x =ᴮ ∅)) )

@[simp]lemma B_ext_a1.ϕ : B_ext a1.ϕ :=
by simp [a1.ϕ]

def a1' : bSet 𝔹 := comprehend a1.ϕ (bv_powerset $ prod omega omega)

def a1.type := a1'.type

def a1.bval := a1'.bval

def a1.ψ (v : bSet 𝔹) : bSet 𝔹 → 𝔹 := λ x, (Ord x ⊓ ⨆ f, is_injective_function x omega f ⊓ image (mem_rel x) (prod omega omega) (prod.map_self x omega f) =ᴮ v ⊓ (- (v =ᴮ ∅)))

@[simp]lemma B_ext_a1.ψ {v : bSet 𝔹} : B_ext (a1.ψ v) :=
by { unfold a1.ψ, apply B_ext_inf, simp, apply B_ext_supr, intro i,
     apply B_ext_inf, swap, simp, apply B_ext_inf, simp, intros x y, tidy_context,
     refine bv_symm _, refine bv_trans (bv_symm a_right) _,
     have : Γ ≤ mem_rel x =ᴮ mem_rel y,
       by { exact B_congr_mem_rel ‹_› },
     have := B_congr_image_left this, show bSet 𝔹, from prod omega omega, show bSet 𝔹, from (prod.map_self x omega i),
     dsimp at this,
     have : Γ ≤ (prod.map_self x omega i) =ᴮ (prod.map_self y omega i),
       by { exact B_congr_prod.map_self_left ‹_› },
     have := B_congr_image_right this, show bSet 𝔹, from (mem_rel y), show bSet 𝔹, from (prod omega omega),
     dsimp at this, bv_cc }

lemma a1'.AE {Γ : 𝔹} : Γ ≤ ⨅ z, z ∈ᴮ a1' ⟹ ⨆ η, Ord η ⊓ ⨆ f, is_injective_function η omega f ⊓ image (mem_rel η) (prod omega omega) (prod.map_self η omega f) =ᴮ z ⊓ (- (z =ᴮ ∅)) :=
begin
  bv_intro z, bv_imp_intro Hz_mem, erw mem_comprehend_iff at Hz_mem,
  bv_cases_at Hz_mem χ Hχ,
  bv_split_at Hχ, bv_split_at Hχ_right, apply bv_rw' Hχ_right_left, simp,
  convert Hχ_right_right, from (bv_powerset $ prod omega omega), simp
end

noncomputable def a1.func : a1.type → bSet 𝔹 := λ χ, classical.some (AE_convert' (a1.ψ) (λ z, B_ext_a1.ψ) a1' (a1'.func χ))

lemma a1.func_spec_aux {χ : a1.type} : ∀ {Γ : 𝔹}, (Γ ≤ ⨅ z, z ∈ᴮ a1' ⟹ ⨆ w, a1.ψ z w) → Γ ≤ (a1'.func χ) ∈ᴮ a1' → Γ ≤ a1.ψ (a1'.func χ) (a1.func χ) :=
by {intro Γ, exact classical.some_spec (a1.func._proof_1 χ)}

lemma a1.func_spec {χ : a1.type} : ∀ {Γ : 𝔹}, Γ ≤ (a1'.func χ) ∈ᴮ a1' → Γ ≤ a1.ψ (a1'.func χ) (a1.func χ) :=
by { intros Γ H_mem, apply a1.func_spec_aux, exact a1'.AE, from ‹_› }

-- equality of pushforward epsilon relation is not enough to guarantee 0 or 1 are in a1,
-- since injectivity fails at 0 and 1 (both epsilon relations are empty)
noncomputable def a1_aux : bSet 𝔹 := ⟨a1.type, a1.func, a1.bval⟩

lemma Ord_of_mem_a1_aux {Γ : 𝔹} {η : bSet 𝔹} (H_mem : Γ ≤ η ∈ᴮ a1_aux) : Γ ≤ Ord η :=
begin
  rw mem_unfold at H_mem, bv_cases_at H_mem χ Hχ, bv_split_at Hχ,
  have : Γ_1 ≤ a1'.func χ ∈ᴮ a1',
    by { convert mem.mk'' _, from ‹_› },
  have := a1.func_spec this, bv_split_at this,
  apply bv_rw' Hχ_right, simp, from ‹_›
end

noncomputable def a1 : bSet 𝔹 := insert 0 (insert 1 a1_aux)

lemma mem_a1_iff₀ { z : bSet 𝔹 } { Γ } : Γ ≤ z ∈ᴮ a1 ↔ Γ ≤ z =ᴮ 0 ⊔ z =ᴮ 1 ⊔ z ∈ᴮ a1_aux :=
by { simp [a1, sup_assoc] }

lemma Ord_of_mem_a1 { Γ : 𝔹 } { η : bSet 𝔹 } (H_mem : Γ ≤ η ∈ᴮ a1) : Γ ≤ Ord η :=
begin
  rw mem_a1_iff₀ at H_mem, bv_or_elim_at H_mem,
    { bv_or_elim_at H_mem.left,
      { apply bv_rw' H_mem.left.left, simp, from Ord_zero },
      { apply bv_rw' H_mem.left.right, simp, from Ord_one }},
    { from Ord_of_mem_a1_aux ‹_› }
end

lemma eq_zero_iff_eq_empty {Γ : 𝔹} { u : bSet 𝔹 } : Γ ≤ u =ᴮ 0 ↔ Γ ≤ u =ᴮ ∅ :=
begin
  refine ⟨_,_⟩; intro H,
    { apply bv_rw' (bv_symm zero_eq_empty), simp, from ‹_› },
    { apply bv_rw' zero_eq_empty, simp, from ‹_› }
end

lemma induced_rel_empty_of_eq_zero
  {η f : bSet 𝔹}
  {Γ : 𝔹}
  (H_func : Γ ≤ is_function η omega f)
  : Γ ≤ η =ᴮ 0 → Γ ≤ induced_epsilon_rel η omega f =ᴮ ∅ :=
begin
  intro H_eq_zero, apply bv_by_contra, bv_imp_intro H_contra,
  rw nonempty_iff_exists_mem at H_contra,
  bv_cases_at H_contra pr Hpr,
  rcases (eq_pair_of_mem_induced_epsilon_rel ‹_›) with ⟨a,b,Ha_mem,Hb_mem,H_eq,Hab⟩,
  replace Hab := induced_epsilon_rel_sub_image_left ‹_› Hab,
  rw mem_image_iff at Hab, cases Hab with _ H_im,
  bv_cases_at H_im z Hz, bv_split_at Hz,
  rw eq_zero_iff_eq_empty at H_eq_zero, rw empty_iff_forall_not_mem at H_eq_zero,
  replace H_eq_zero := H_eq_zero z, exact bv_absurd _ Hz_left ‹_›
end

lemma nonempty_of_induced_rel_nonempty
  {η f : bSet 𝔹}
  {Γ : 𝔹}
  (H_func : Γ ≤ is_function η omega f)
  : Γ ≤ -(induced_epsilon_rel η omega f =ᴮ ∅) → Γ ≤ -(η =ᴮ ∅) :=
begin
  intro H, rw ←imp_bot, bv_imp_intro H',
  rw ← eq_zero_iff_eq_empty at H',
  have := induced_rel_empty_of_eq_zero ‹_› ‹_›, bv_contradiction
end

lemma not_zero_of_induced_rel_nonempty
  {η f : bSet 𝔹}
  {Γ : 𝔹}
  (H_func : Γ ≤ is_function η omega f)
  : Γ ≤ -(induced_epsilon_rel η omega f =ᴮ ∅) → Γ ≤ -(η =ᴮ 0) :=
begin
  intro H', apply @bv_rw' _ _ _ _ _ (zero_eq_empty) (λ w, - (η =ᴮ w)), {simp},
  exact nonempty_of_induced_rel_nonempty ‹_› ‹_›
end

lemma not_one_of_induced_rel_nonempty
  {η f : bSet 𝔹}
  {Γ : 𝔹}
  (H_func : Γ ≤ is_function η omega f)
  : Γ ≤ -(induced_epsilon_rel η omega f =ᴮ ∅) → Γ ≤ -(η =ᴮ 1) :=
begin
  intro H, rw nonempty_iff_exists_mem at H, bv_cases_at H pr Hpr,
  rcases eq_pair_of_mem_induced_epsilon_rel Hpr with ⟨a,b,Ha,Hb,H_eq,Hab⟩,
  rw mem_induced_epsilon_rel_iff at Hab, rcases Hab with ⟨Ha, Hb, Hab⟩,
  bv_cases_at' Hab a' Ha', bv_split_at Ha',
  bv_cases_at' Ha'_right b' Hb', bv_split_at Hb', bv_split_at Hb'_right, bv_split_at Hb'_right_left,
  rw ←imp_bot, bv_imp_intro' H_eq_one,
  suffices : Γ_4 ≤ 0 ∈ᴮ 0,
    by { exact bot_of_mem_self' ‹_› },
  suffices : Γ_4 ≤ a' =ᴮ 0 ∧ Γ_4 ≤ b' =ᴮ 0,
    by { change _ ≤ (λ (w : bSet 𝔹), w ∈ᴮ 0) 0, apply bv_rw' (bv_symm this.left), simp,
         change _ ≤ (λ w, a' ∈ᴮ w) _, apply bv_rw' (bv_symm this.right), simpa },
  refine ⟨_,_⟩,
    { apply eq_zero_of_mem_one, have := mem_domain_of_is_function ‹Γ_4 ≤ pair a' a ∈ᴮ f› ‹_›, bv_cc },
    { apply eq_zero_of_mem_one, have := mem_domain_of_is_function ‹Γ_4 ≤ pair b' b ∈ᴮ f› ‹_›, bv_cc },
  from ‹_›
end

lemma nonempty_induced_rel_iff_not_zero_and_not_one
  {η f : bSet 𝔹}
  {Γ : 𝔹}
  (H_ord : Γ ≤ Ord η)
  (H_inj : Γ ≤ is_function η omega f)
  : Γ ≤ -((induced_epsilon_rel η omega f) =ᴮ ∅) ↔ (Γ ≤ -(η =ᴮ 0) ∧ Γ ≤ -(η =ᴮ 1)) :=
begin
  refine ⟨_,_⟩; intro H,
    { refine ⟨_,_⟩,
    { exact not_zero_of_induced_rel_nonempty ‹_› ‹_› },
      { exact not_one_of_induced_rel_nonempty ‹_› ‹_› }},
    { cases H with H₁ H₂, rw nonempty_iff_exists_mem,
      have := one_mem_of_not_zero_and_not_one ‹_› H₁ H₂,
      have Hmem_one : Γ ≤ _ := zero_mem_one,
      have H_zero_mem : Γ ≤ 0 ∈ᴮ η,
        by { exact mem_of_mem_Ord ‹_› ‹_ ≤ 1 ∈ᴮ η› ‹_›},
      refine bv_use _,
      swap, apply mem_induced_epsilon_rel_of_mem H_zero_mem this ‹_›, from ‹_› }
end

/--
  a1 contains every ordinal η which injects into ω
-/
lemma mem_a1_of_injects_into_omega_aux {Γ : 𝔹} {η : bSet 𝔹} (H_ord : Γ ≤ Ord η) (H_inj : Γ ≤ ⨆ f, is_injective_function η omega f) (H_not_zero : Γ ≤ - (η =ᴮ 0)) (H_not_one : Γ ≤ -(η =ᴮ 1)) : Γ ≤ η ∈ᴮ a1_aux :=
begin
  bv_cases_at H_inj f Hf,
  rw mem_unfold', let R := (induced_epsilon_rel η omega f),
  have : Γ_1 ≤ R ∈ᴮ a1',
    by { erw mem_comprehend_iff₂, apply bv_use R, refine le_inf _ (le_inf bv_refl _),
         { rw mem_powerset_iff, apply subset.mk_subset },
         { apply bv_use η, refine le_inf ‹_› _, apply bv_use f,
           refine le_inf (le_inf ‹_› bv_refl) _,
           erw nonempty_induced_rel_iff_not_zero_and_not_one, simp*, from ‹_›, from bv_and.left ‹_› },
         simp },
  rw mem_unfold at this, bv_cases_at this χ Hχ,
  apply bv_use (a1.func χ), bv_split_at Hχ, refine le_inf _ _,
  convert mem.mk'' _, refl, from ‹_›,
  have H_mem : Γ_2 ≤ (a1'.func χ) ∈ᴮ a1', from mem.mk'' ‹_›,
  have := a1.func_spec H_mem,
  bv_split_at this,
  bv_cases_at this_right g Hg, bv_split_at Hg,
  bv_split_at Hg_left,
  apply eq_of_eq_induced_epsilon_rel, from ‹_›,
  {apply Ord_of_mem_a1_aux, convert mem.mk'' _, refl, from ‹_›},
  from Hf, from Hg_left_left,
  { dsimp [R] at Hχ_right,change _ ≤ induced_epsilon_rel _ _ _ =ᴮ _ at Hg_left_right, bv_cc },
  { rw exists_two_iff; from ‹_› },
  rw exists_two_iff,
  suffices : Γ_3 ≤ -(image (mem_rel (a1.func χ)) (prod omega omega) (prod.map_self (a1.func χ) omega g) =ᴮ ∅),
    by { erw nonempty_induced_rel_iff_not_zero_and_not_one at this, cases this with this₁ this₂,
         from ‹_›, from ‹_›, from bv_and.left ‹_› },
  apply @bv_rw' _ _ _ _ _ Hg_left_right (λ w, -(w =ᴮ ∅)), simp, from ‹_›, from ‹_›
end

lemma mem_a1_iff {Γ : 𝔹} {η : bSet 𝔹} (H_ord : Γ ≤ Ord η) : Γ ≤ η ∈ᴮ a1 ↔ Γ ≤ ⨆f, is_injective_function η omega f :=
begin
  refine ⟨_,_⟩,
    { intro H_mem,
      rw mem_a1_iff₀ at H_mem,
      bv_or_elim_at H_mem, bv_or_elim_at H_mem.left,
        { apply injection_into_of_injects_into, apply injects_into_of_subset,
          apply bv_rw' H_mem.left.left, simp, apply of_nat_subset_omega },
        { apply injection_into_of_injects_into, apply injects_into_of_subset,
          apply bv_rw' H_mem.left.right, simp, apply of_nat_subset_omega },
        { rw mem_unfold at H_mem.right, bv_cases_at H_mem.right χ Hχ,
      bv_split_at Hχ,
      have : Γ_2 ≤ a1'.func χ ∈ᴮ a1',
        by { from mem.mk'' ‹_› },
      have := a1.func_spec this,
      apply bv_rw' Hχ_right, simp,
      bv_split_at this, bv_cases_at this_right f Hf, apply bv_use f,
      exact bv_and.left (bv_and.left ‹_›) }},
    { intro H_ex, rw mem_a1_iff₀, bv_cases_on η =ᴮ 1,
      { exact bv_or_left (bv_or_right ‹_›) },
      { bv_cases_on η =ᴮ 0,
        { exact bv_or_left (bv_or_left ‹_›) },
        { refine bv_or_right _, apply mem_a1_of_injects_into_omega_aux, repeat { assumption }}}}
end

lemma a1_transitive {Γ} : Γ ≤ is_transitive a1 :=
begin
  bv_intro z, bv_imp_intro Hz_mem,
  rw subset_unfold', bv_intro w, bv_imp_intro Hw_mem,
  rw mem_a1_iff _, swap,
    { refine Ord_of_mem_Ord Hw_mem _, from Ord_of_mem_a1 ‹_› },
    { have Hz_ord : Γ_2 ≤ Ord z := Ord_of_mem_a1 ‹_›,
      rw (mem_a1_iff ‹_›) at Hz_mem,
      cases (exists_convert Hz_mem) with f Hf,
      have Hw_sub : Γ_2 ≤ w ⊆ᴮ z,
        by {apply subset_of_mem_transitive, from bv_and.right ‹_›, from ‹_› },
      have Hw_inj : Γ_2 ≤ injection_into w z := injection_into_of_subset Hw_sub,
      cases (exists_convert Hw_inj) with g Hg,
      apply bv_use (injective_function_comp Hg Hf), apply injective_function_comp_is_injective_function }
end

lemma a1_ewo {Γ} : Γ ≤ ewo a1 :=
begin
  refine le_inf _ _,
    { apply epsilon_trichotomy_of_sub_Ord, bv_intro x, bv_imp_intro H_mem,
      from Ord_of_mem_a1 ‹_› },
    { apply epsilon_wf_of_sub_Ord }
end

lemma a1_Ord {Γ : 𝔹} : Γ ≤ Ord a1 := le_inf a1_ewo a1_transitive

lemma a1_not_le_omega {Γ : 𝔹} : Γ ≤ -(a1 ≼ omega) :=
begin
  rw ←imp_bot, bv_imp_intro H_contra, rw injects_into_iff_injection_into at H_contra,
  erw ←mem_a1_iff (a1_Ord) at H_contra, from bot_of_mem_self' ‹_›
end

lemma a1_spec {Γ : 𝔹} : Γ ≤ aleph_one_Ord_spec a1 :=
begin
  refine le_inf (a1_not_le_omega) _,
  refine le_inf a1_Ord _,
  bv_intro η, bv_imp_intro Ord_η, bv_imp_intro H,
  classical,
  by_cases ⊥ < Γ_2,
   { rw (Ord.le_iff_lt_or_eq a1_Ord ‹_›),
     apply bv_by_contra, bv_imp_intro H_contra,
     simp only [le_inf_iff] with bv_push_neg at H_contra,
     cases H_contra with H_contra₁ H_contra₂,
     suffices : Γ_3 ≤ injects_into η omega,
       by exact bv_absurd _ this ‹_›,
     suffices : Γ_3 ≤ η ∈ᴮ a1,
       by {replace this := (mem_a1_iff ‹_›).mp this, bv_cases_at this f Hf,
           apply bv_use f,
             from le_inf (is_func'_of_is_injective_function ‹_›) (bv_and.right ‹_›) },
     have : Γ_3 ≤ _ := Ord.trichotomy a1_Ord Ord_η,
     apply bv_by_contra, bv_imp_intro H_contra₃,
     bv_or_elim_at this,
       { bv_or_elim_at this.left,
         { bv_contradiction },
         { bv_contradiction }},
       { bv_contradiction } },
    { have : Γ_2 ≤ ⊥ := le_bot_iff_not_bot_lt.mp h,
      from le_trans this bot_le }
end

lemma a1_le_of_omega_lt {Γ : 𝔹} : Γ ≤ le_of_omega_lt a1 :=
begin
  bv_intro x, bv_imp_intro H_Ord, bv_imp_intro H_no_surj,
  have H_no_inj : Γ_2 ≤ -(injects_into x omega),
    by { rw ←imp_bot, bv_imp_intro H_contra,
         refine bv_absurd _ _ H_no_surj,
         bv_cases_on x =ᴮ ∅,
         { apply bv_use (∅ : bSet 𝔹), apply bv_use (∅ : bSet 𝔹),
          refine le_inf _ _,
          refine le_inf empty_subset _,
          exact is_func'_empty,
          apply bv_rw' H.left, simp, apply is_surj_empty },
         { apply larger_than_of_surjects_onto,
           refine surjects_onto_of_injects_into ‹_› _, rwa ←nonempty_iff_exists_mem } },
  have H_not_mem_a1 : Γ_2 ≤ -(x ∈ᴮ a1),
    by { rw ←imp_bot, bv_imp_intro H_contra, rw mem_a1_iff ‹_›at H_contra,
         have := injects_into_of_injection_into H_contra, bv_contradiction },
  refine injects_into_of_subset _,
  rw Ord.le_iff_lt_or_eq (a1_Ord) ‹_›,
  have := Ord.trichotomy (a1_Ord) ‹_›,
  bv_or_elim_at this, bv_or_elim_at this.left,
    { from bv_or_right ‹_› },
    { from bv_or_left ‹_› },
    { from bv_exfalso (by bv_contradiction) }
end

end a1

section

variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

lemma injects_into_omega_of_mem_aleph_one_check {Γ : 𝔹} {z : bSet 𝔹} (H_mem : Γ ≤ z ∈ᴮ (ℵ₁)̌ ): Γ ≤ injects_into z bSet.omega :=
begin
  rw mem_unfold at H_mem, bv_cases_at H_mem η Hη, simp at Hη,
  suffices : Γ_1 ≤ injects_into (ℵ₁̌.func η) bSet.omega,
  apply bv_rw' Hη, simp, from ‹_›,
  suffices : pSet.injects_into ((ℵ₁).func $ check_cast η) pSet.omega,
    by {rw check_func, apply check_injects_into, from ‹_› },
  refine pSet.injects_into_omega_of_mem_aleph_one _,
    { simp }
end

lemma mem_aleph_one_of_injects_into_omega {x : bSet 𝔹} {Γ : 𝔹} (H_aleph_one : Γ ≤ aleph_one_Ord_spec x) {z : bSet 𝔹} (H_x_Ord : Γ ≤ Ord x) (H_z_Ord : Γ ≤ Ord z) (H_inj : Γ ≤ injects_into z bSet.omega) : Γ ≤ z ∈ᴮ x :=
begin
  apply bv_by_contra, bv_imp_intro H_contra,
  have := Ord.resolve_lt H_z_Ord H_x_Ord H_contra,
  rw ← Ord.le_iff_lt_or_eq H_x_Ord H_z_Ord at this,
  suffices H_inj_omega : Γ_1 ≤ injects_into x omega,
    by {refine bv_absurd _ H_inj_omega _, from bv_and.left ‹_› },
  exact injects_into_trans (injects_into_of_subset this) (H_inj)
end

lemma aleph_one_check_sub_aleph_one_aux {x : bSet 𝔹} {Γ : 𝔹} (H_ord : Γ ≤ Ord x) (H_aleph_one : Γ ≤ aleph_one_Ord_spec x) : Γ ≤ ℵ₁̌ ⊆ᴮ x :=
begin
  rw subset_unfold', bv_intro w, bv_imp_intro H_mem_w,
  apply mem_aleph_one_of_injects_into_omega, from ‹_›, from ‹_›,
  exact Ord_of_mem_Ord H_mem_w
    (check_Ord (by {unfold pSet.aleph_one pSet.card_ex, simp })),
  exact injects_into_omega_of_mem_aleph_one_check ‹_›
end

end

end bSet