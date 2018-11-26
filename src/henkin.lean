import .fol order.zorn order.filter logic.basic data.finset data.set tactic.tidy .completion .language_extension .colimit .to_mathlib tactic.linarith

-- local attribute [instance] classical.prop_decidable

open fol

universes u v
local infix ` →ᴸ `:10 := Lhom -- \^L

/- Temporarily putting this here because I can't get Lean to recognize Lhom in colimit.lean -/
namespace colimit

export directed_type
/- Below we define colimits of languages. These are just fieldwise (and then indexwise)
   colimits of types, so the proofs are very similar. -/

local infix ` ∘ `:60 := Lhom.comp

structure directed_diagram_language (D : (directed_type.{u})) : Type (max (u+1) (v+1)) :=
  (obj : D.carrier → (Language.{v}))
  (mor : ∀{x}, ∀{y}, D.rel x y → (obj x →ᴸ obj y))
  (h_mor : ∀{x} {y} {z} {f1 : D.rel x y} {f2 : D.rel y z} {f3 : D.rel x z},
            (mor f3) = (mor f2) ∘ (mor f1)) -- functoriality

export directed_diagram_language

/- Given a directed diagram of languages, we obtain two ℕ-indexed families of
   directed diagrams of types: one by restricting to functions and one by
   restricting to relations. -/
@[reducible]def diagram_functions {D : (directed_type)} {F : (directed_diagram_language D)} (n : ℕ) :
                      ((directed_diagram D)) :=
begin
  refine ⟨by {intro x, exact (obj F x).functions n},_,_⟩,
  {intros x y edge, have := (F.mor edge).on_function, exact @this n},
  {intros, simp only [], have := F.h_mor, have := @this x y z f1 f2 f3, rw[this]},
end

@[reducible]def diagram_relations {D : (directed_type)} {F : (directed_diagram_language D)} (n : ℕ) :
                      ((directed_diagram D)) :=
begin
  refine ⟨by {intro x, exact (obj F x).relations n},_,_⟩,
  {intros x y edge, have := (F.mor edge).on_relation, exact @this n},
  {intros, simp only [], have := F.h_mor, have := @this x y z f1 f2 f3, rw[this]},
end

def coproduct_of_directed_diagram_language {D : (directed_type : Type (u+1)) }
    (F : (directed_diagram_language D :  Type (max (u+1) (v+1)))) :  Language :=
⟨λn, coproduct_of_directed_diagram (@diagram_functions D F n),
  λn, coproduct_of_directed_diagram (@diagram_relations D F n)⟩

def colimit_language {D : (directed_type : Type (u+1)) } (F : (directed_diagram_language D)) : Language :=
⟨λn, @quotient (coproduct_of_directed_diagram (@diagram_functions D F n))
  ⟨germ_relation (diagram_functions n), germ_equivalence (diagram_functions n)⟩,
λn, @quotient (coproduct_of_directed_diagram (@diagram_relations D F n))
  ⟨germ_relation (diagram_relations n), germ_equivalence (diagram_relations n)⟩⟩

/- The canonical map of languages is the pointwise canonical map of colimits of types -/
def canonical_map_language {D} {F : directed_diagram_language D} (i : D.carrier) :
                           (F.obj i) →ᴸ colimit_language F :=
⟨λ n, function.comp (by apply quotient.mk) (@canonical_inclusion_coproduct D (diagram_functions n) i),
λ n, function.comp (by apply quotient.mk) (@canonical_inclusion_coproduct D (diagram_relations n) i)⟩

end colimit

open colimit

/- The Henkin construction consists of the following:
   1. Constructing a ℕ-indexed chain of languages and theories, and
   2. Taking the union of that chain. -/

/- To define henkin_language_step, there is an inductive type of new function
   function symbols, comprising an inclusion constructor for the symbols
   from L, and a witness constructor which introduces witnesses for every
   bounded_formula 1-/
inductive henkin_language_functions (L : (Language : Type (u+1))) : ℕ → Type u
  | inc : ∀ {n}, (L.functions n) → henkin_language_functions n
  | wit : (bounded_formula L 1) → henkin_language_functions 0

export henkin_language_functions

/- The basic step of the Henkin construction on languages.
   Given a language L, return a language L' with constants
   witnessing all bounded_formula 1-/
def henkin_language_step (L : (Language : Type (u+1))) : (Language : Type (u+1)) :=
  ⟨henkin_language_functions L, L.relations⟩

def wit' {L : Language} :
(bounded_formula L 1) →(henkin_language_step L).functions 0 :=
by {intro f, fapply wit, exact f}

def henkin_language_inclusion {L : Language} : L →ᴸ (henkin_language_step L) :=
  ⟨λ n f, inc f, λn, id⟩

lemma henkin_language_inclusion_inj {L : Language} : Lhom.is_injective (@henkin_language_inclusion L) :=
begin
  split, all_goals{intro n, intros x y H, try{exact H}},
  fapply @henkin_language_functions.inc.inj_arrow,
  exact L, exact n, exact x, exact y, exact H, simp only [imp_self]
end

/- The basic step of the Henkin construction on theories.
   Given an L-theory T, return an L'-theory T' which is T expanded by
   sentences saying that the new witnesses are witnesses. -/
def henkin_theory_step {L} (T : Theory L) : Theory $ henkin_language_step L :=
begin
  refine _ ∪ (Theory_induced henkin_language_inclusion T),
  refine _ '' (set.univ : set $ bounded_formula L 1),
  intro f, let c := bd_func (wit' f),
  let f' := Lhom.on_bounded_formula henkin_language_inclusion f,
  exact ∃'f' ⇔ f'[c /0],
end

local notation `ℕ'` := (ulift.{(u+2)} directed_type_of_nat)

def henkin_language_chain_objects {L : Language} : ℕ → Language
  | 0 := L
  | (n+1) := henkin_language_step (henkin_language_chain_objects n)

local infix ` ∘ `:60 := Lhom.comp

@[elab_as_eliminator]def henkin_language_chain_maps (L : Language): Π x y, x ≤ y → (@henkin_language_chain_objects L x →ᴸ @henkin_language_chain_objects L y)
| x 0 H := by {have : x = 0, by exact nat.eq_zero_of_le_zero H, rw[this], apply Lhom.id}
| x (y+1) H := by {by_cases x = y + 1, rw[h], fapply Lhom.id,
               refine @henkin_language_inclusion (@henkin_language_chain_objects L y) ∘ _,
               fapply henkin_language_chain_maps,
               simp only [*, nat.lt_of_le_and_ne, nat.le_of_lt_succ, ne.def, not_false_iff]}

lemma henkin_language_chain_maps_inj (L : Language) : Π x y : ℕ, Π (h : x ≤ y), Lhom.is_injective (henkin_language_chain_maps L x y h) :=
begin
  intros i j h, split, swap,
  {induction j,
    {have : i  = 0, by exact nat.eq_zero_of_le_zero h, subst this,
    intros n x y H, exact H},
    {by_cases i = (j_n + 1), dedup,
     {subst h_1, rw[henkin_language_chain_maps], simp*,
     intros n x y H, exact H},
     {have : i ≤ j_n, by simp only [*, nat.le_of_lt_succ, nat.lt_of_le_and_ne, ne.def, not_false_iff],
     have ih := j_ih this, show ℕ, exact i,
     rw[henkin_language_chain_maps], simp only [*, dif_neg, not_false_iff],
     intro n, fapply function.injective_comp, fapply henkin_language_inclusion_inj.on_relation,
     change function.injective (Lhom.on_relation (henkin_language_chain_maps L i j_n this)),
     simp only *,}}
  },
  {induction j,
    {have : i  = 0, by exact nat.eq_zero_of_le_zero h, subst this,
    intros n x y H, exact H},
    {by_cases i = (j_n + 1), dedup,
     {subst h_1, rw[henkin_language_chain_maps], simp*,
     intros n x y H, exact H},
     {have : i ≤ j_n, by simp only [*, nat.le_of_lt_succ, nat.lt_of_le_and_ne, ne.def, not_false_iff],
     have ih := j_ih this, show ℕ, exact i,
     rw[henkin_language_chain_maps], simp only [*, dif_neg, not_false_iff],
     intro n, fapply function.injective_comp, fapply henkin_language_inclusion_inj.on_function,
     change function.injective (Lhom.on_function (henkin_language_chain_maps L i j_n this)),
     simp only *,}}},
end

/- Given a language, iterate henkin_language_step, returning this data in the form
   of a directed diagram of types indexed by ℕ' -/
def henkin_language_chain {L : Language} : (directed_diagram_language directed_type_of_nat) := 
begin
  refine ⟨_, _, _⟩,
  {exact @henkin_language_chain_objects L},
  {change Π {x y : ℕ},
    x ≤ y → (henkin_language_chain_objects x →ᴸ henkin_language_chain_objects y),
    intros x y H, fapply henkin_language_chain_maps, exact H},
  {change ∀ {x y z : ℕ} {f1 :  x ≤ y} {f2 :  y ≤ z}
  {f3 :  x ≤ z},
    henkin_language_chain_maps L x z _ =
    henkin_language_chain_maps L y z _ ∘
    henkin_language_chain_maps L x y _,
    intros x y z f1 f2 f3,
    induction z,
      {have this1 : x = 0, by exact nat.eq_zero_of_le_zero f3,
      have this2 : y = 0, by exact nat.eq_zero_of_le_zero f2,
       subst this1, subst this2, refl},
      { unfold henkin_language_chain_maps, by_cases y = z_n + 1, simp*, subst h, by_cases x = z_n+1, simp*, subst h,
       unfold henkin_language_chain_maps, simp, refl,
       {simp*,
       have : eq.mpr _ (Lhom.id (henkin_language_chain_objects (z_n + 1))) ∘ henkin_language_chain_maps L x (z_n + 1) f1 = (Lhom.id (henkin_language_chain_objects (z_n + 1))) ∘ henkin_language_chain_maps L x (z_n + 1) f1, by refl, rw[this],
       have : Lhom.id (henkin_language_chain_objects (z_n + 1)) ∘ henkin_language_chain_maps L x (z_n + 1) f1 =  henkin_language_chain_maps L x (z_n + 1) f1,
       by simp only [eq_self_iff_true, fol.Lhom.id_is_left_identity],
       rw[this], unfold henkin_language_chain_maps, simp*,
         },
       {by_cases x = z_n+1,
         {simp*, have : y < z_n+1, by {fapply nat.lt_of_le_and_ne,
         repeat{assumption}}, exfalso, linarith},
         {simp*, have Hxy : x ≤ z_n ∧ y ≤ z_n,
         by simp only [*, nat.le_of_lt_succ, nat.lt_of_le_and_ne, ne.def, not_false_iff, and_self],
         simp only [*, eq_self_iff_true, not_false_iff]}
       }
    }
}
end

def L_infty (L) : Language :=
   colimit_language $ @henkin_language_chain L

/- For every n : ℕ, return the canonical inclusion L_n → L_infty  -/
def henkin_language_canonical_map {L : Language} (m : ℕ) : (@henkin_language_chain L).obj m →ᴸ (@L_infty L) := by apply canonical_map_language

/- To prove that T_infty is Henkin, we'll have to exhibit a witnessing function of the form
  wit : bounded_formula 1 → L_infty.constants.

  To do this, we have to recursively go through formulas and terms and show that for every
  formula, there exists some N such that all the symbols in that formula were contained in L_N,
  and therefore, the wit function for L_N introduces the constant we want.

  The natural way to proceed is to define the induced colimit on bounded_formulas.

  Then, we can define the required wit function by taking a bounded formula, picking a
  representative from stage N, applying the wit function from stage N, and then pushing
  it up to L_infty. -/

def henkin_bounded_formula_chain {L : Language} : directed_diagram directed_type_of_nat :=
begin
  refine ⟨λ n, bounded_formula (@henkin_language_chain_objects L n) 1, _, _⟩,
  {intros x y H, apply Lhom.on_bounded_formula, apply @henkin_language_chain_maps L, exact H},
  {intros x y z f1 f2 f3, dsimp only [*],
   have : (henkin_language_chain_maps L x z f3) =
   (henkin_language_chain_maps L y z f2) ∘ (henkin_language_chain_maps L x y f1),
   fapply henkin_language_chain.h_mor, rw[this, Lhom.comp_on_bounded_formula]}
end

/- Not really a chain, since we haven't set up interpretations of theories yet -/
def henkin_theory_chain {L : Language} {T : Theory L}: Π(n : ℕ), (Theory (obj (@henkin_language_chain L) n))
| 0 := T
| (n+1) := henkin_theory_step (henkin_theory_chain n)

/- Now we have to push all these theories into Theory L_∞, so that they literally become a chain
   of sets. -/

/- Given T_n from henkin_theory_chain, ι T_n is the expansion of T_n to an L_infty theory -/
def ι {L : Language} {T : Theory L} (m : ℕ) :  Theory (L_infty L) :=
(Lhom.on_sentence (@henkin_language_canonical_map L m)) '' (@henkin_theory_chain L T m)

/- T_infty is the henkinization of T; we define it to be the union ⋃ (n : ℕ), ι(T n). -/
def T_infty {L : Language} (T : Theory L) : Theory (L_infty L) := set.Union (@ι L T)

def henkin_language {L} {T : Theory L} {hT : is_consistent T} : Language := L_infty L

local infix ` →ᴸ `:10 := Lhom -- \^L

/- I dislike this proof, but I don't know how apply canonical_map_language otherwise... -/
def henkin_language_over {L} {T : Theory L} {hT : is_consistent T} : L →ᴸ (@henkin_language L T hT) := begin
change (henkin_language_chain.obj (0 : ℕ)) →ᴸ colimit_language henkin_language_chain,
apply canonical_map_language
end

lemma henkin_language_over_injective {L} {T : Theory L} {hT : is_consistent T} : Lhom.is_injective (@henkin_language_over L T hT) :=
begin
  split, all_goals{intro n, unfold henkin_language_over canonical_map_language, simp,
  rw[<-canonical_map], fapply colimit.canonical_map_inj_of_transition_maps_inj, intros i j H,
  dsimp[diagram_functions, diagram_relations, henkin_language_chain],
  simp only [henkin_language_chain_maps_inj, Lhom.is_injective.on_function, Lhom.is_injective.on_relation]}
end

def complete_henkin_Theory_over {L : Language} (T : Theory L) (hT : is_consistent T) : Type u := Σ' T' : Theory_over T hT, has_enough_constants T'.val ∧ is_complete T'.val

def henkinization {L : Language} {T : Theory L} {hT : is_consistent T} : Theory (@henkin_language L T hT) := T_infty T

lemma henkinization_is_henkin {L : Language} {T : Theory L} {hT : is_consistent T} : has_enough_constants (@henkinization L T hT) :=
begin
  unfold henkinization T_infty has_enough_constants, split, swap,
  sorry -- here, we need to define the witnessing function at L_infty
end

/- It looks like this is the lemma which requires reflect_prf -/
lemma henkinization_consistent {L : Language} {T : Theory L} {hT : is_consistent T} : is_consistent (@henkinization L T hT) := sorry

noncomputable def complete_henkinization {L} {T : Theory L} {hT : is_consistent T} := completion_of_consis _ (@henkinization L T hT) henkinization_consistent

/- Bundled versions below -/
def Language_over (L : Language) := Σ L' : Language, L →ᴸ L'

def henkin_Theory_over {L : Language} (T : Theory L) (hT : is_consistent T) : Type u := Σ' T' : Theory_over T hT, has_enough_constants T'.val
/-- Given an L-theory T, return a larger language L' and a Henkin theory T' extending T viewed as an L'-theory --/
def henkinization' {L : Language} {T : Theory L} (hT : is_consistent T) : Σ (L' : Language_over L), henkin_Theory_over (Theory_induced L'.snd T) begin apply consis_Theory_induced_of_consis, repeat{assumption} end := sorry

/-- The completion of a Henkin theory is again Henkin. --/
lemma has_enough_constants_of_completion {L} {T : Theory L} {hT : is_consistent T} : is_consistent (completion_of_consis _ (@henkinization L T hT) henkinization_consistent).fst.val := sorry

/-- Given an L-theory T, return a completed Henkinization of T --/
def complete_henkinization' {L : Language} {T : Theory L} (hT : is_consistent T) : Σ (L' : Language_over L), complete_henkin_Theory_over (Theory_induced L'.snd T) begin apply consis_Theory_induced_of_consis, repeat{assumption} end := sorry
