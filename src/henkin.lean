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
  {intros x y edge, have := (F.mor edge).on_function, exact this },
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

-- structure cocone_language' {D} (F : directed_diagram_language D) :=
--   (vertex : Language)
--   (cocone_functions : ∀{n}, @colimit.cocone D (@diagram_functions D F n)
-- would need extra hypotheses that for every n, the vertex of the cocone_functions (resp. relations)
-- is equal to vertex.functions (resp. relations)
-- maybe that would have been easier to work with

structure cocone_language {D} (F : directed_diagram_language D) :=
  (vertex : Language)
  (map : Π i : D.carrier, F.obj i →ᴸ vertex)
  (h_compat : ∀{i}, ∀{j}, Π h : D.rel i j, (map i ) = (map j) ∘ (F.mor h))

export cocone_language

def cocone_of_colimit_language {D} (F : directed_diagram_language D) : cocone_language F :=
begin
  refine ⟨colimit_language F, canonical_map_language, _⟩, intros i j H, fapply Lhom.Lhom_funext,
  all_goals{fapply funext, intro n,
  simp only [quotient.eq,(≈),canonical_map_language,function.comp], have h_refl : D.rel j j,
  by apply D.h_reflexive, -- refine ⟨j,F.mor H x, H, h_refl, rfl, _⟩,
  fapply funext, intro x, simp only [quotient.eq,(≈),canonical_map_language,function.comp], 
  },
  {refine ⟨j,(F.mor H).on_function x, H, h_refl, rfl, _⟩,
  change (function.comp ((diagram_functions n).mor h_refl) begin fapply Lhom.on_function, exact @mor D F i j H, end) x = (F.mor H).on_function x,
   have := Lhom.comp_on_function' (F.mor h_refl) (F.mor H) n, rw[<-this,<-F.h_mor]},
  {  refine ⟨j,(F.mor H).on_relation x, H, h_refl, rfl, _⟩,
    change (function.comp ((diagram_relations n).mor h_refl) begin fapply Lhom.on_relation, exact @mor D F i j H, end) x = (F.mor H).on_relation x,
   have := Lhom.comp_on_relation' (F.mor h_refl) (F.mor H) n, rw[<-this,<-F.h_mor]}
end

/- Given a cocone V over a diagram D, return the canonical map colim D → V-/
def universal_map_language {D} {F : directed_diagram_language D} {V : cocone_language F} : colimit_language F →ᴸ (V.vertex) :=
begin
  split, all_goals{intro n,
  fapply quotient.lift},

{exact λp, begin fapply @Lhom.on_function, exact F.obj p.fst, exact @map D F V p.fst, exact p.snd end},
  {intros p q H, rcases p with ⟨i,x⟩, rcases q with ⟨j,y⟩, simp only *,
   simp[(≈), germ_relation] at H, rcases H with ⟨k,z,⟨f1, H1⟩,f2,H2⟩,
   change (V.map i).on_function x = (V.map j).on_function y, have : (V.map i).on_function x = (V.map k).on_function ((F.mor f1).on_function x),
   simp only [V.h_compat f1, eq_self_iff_true, function.comp_app],
   have : (V.map j).on_function y = (V.map k).on_function ((F.mor f2).on_function y),
   simp only [V.h_compat f2, eq_self_iff_true, function.comp_app],
   simp only [*, eq_self_iff_true]},

{exact λp, begin fapply @Lhom.on_relation, exact F.obj p.fst, exact @map D F V p.fst, exact p.snd end},
  {intros p q H, rcases p with ⟨i,x⟩, rcases q with ⟨j,y⟩, simp only *,
   simp[(≈), germ_relation] at H, rcases H with ⟨k,z,⟨f1, H1⟩,f2,H2⟩,
   change (V.map i).on_relation x = (V.map j).on_relation y, have : (V.map i).on_relation x = (V.map k).on_relation ((F.mor f1).on_relation x),
   simp only [V.h_compat f1, eq_self_iff_true, function.comp_app],
   have : (V.map j).on_relation y = (V.map k).on_relation ((F.mor f2).on_relation y),
   simp only [V.h_compat f2, eq_self_iff_true, function.comp_app],
   simp only [*, eq_self_iff_true]},
end

end colimit

open colimit

/- The Henkin construction consists of the following:
   1. Constructing a ℕ-indexed chain of languages and theories, and
   2. Taking the union of that chain. -/

/- To define henkin_language_step, there is an inductive type of new function
   function symbols, comprising an inclusion constructor for the symbols
   from L, and a witness constructor which introduces witnesses for every
   bounded_formula 1-/
inductive henkin_language_functions (L : Language.{u}) : ℕ → Type u
  | inc : ∀ {n}, L.functions n → henkin_language_functions n
  | wit : bounded_formula L 1 → henkin_language_functions 0

open henkin_language_functions

/- The basic step of the Henkin construction on languages.
   Given a language L, return a language L' with constants
   witnessing all bounded_formula 1-/
@[reducible]def henkin_language_step (L : Language.{u}) : Language.{u} :=
  ⟨henkin_language_functions L, L.relations⟩

def wit' {L : Language} : bounded_formula L 1 → (henkin_language_step L).constants := wit

def henkin_language_inclusion {L : Language} : L →ᴸ henkin_language_step L :=
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
@[reducible]def wit_property {L : Language} (f : bounded_formula L 1) (c : L.constants) : 
  sentence L :=
(∃'f) ⟹ f[bd_const c/0]

open fol.Lhom
def henkin_theory_step {L} (T : Theory L) : Theory $ henkin_language_step L :=
Theory_induced henkin_language_inclusion T ∪ 
(λ f : bounded_formula L 1, 
  wit_property (henkin_language_inclusion.on_bounded_formula f) (wit' f)) '' (set.univ : set $ bounded_formula L 1)

def is_consistent_henkin_theory_step{L} {T : Theory L} (hT : is_consistent T) :
  is_consistent (henkin_theory_step T) :=
begin
  apply is_consistent_union,
  { exact is_consistent_Theory_induced henkin_language_inclusion_inj hT },
  { intros ψ hψ, rcases hψ with ⟨ψ', x, hψ'⟩, sorry }
end

@[reducible]def henkin_language_chain_objects {L : Language} : ℕ → Language
  | 0 := L
  | (n+1) := henkin_language_step (henkin_language_chain_objects n)

@[simp]lemma obvious {L : Language} {i : ℕ} : henkin_language_functions (@henkin_language_chain_objects L i) 0 = (@henkin_language_chain_objects L (i+1)).constants :=
by refl 

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



@[simp]lemma id_of_self_map (L : Language) : ∀ k, (henkin_language_chain_maps L k k (le_refl k)) = Lhom.id ((@henkin_language_chain L).obj k)
| 0 := by refl
| (n+1) := by {dsimp[henkin_language_chain_maps], simp*, refl}

@[simp]lemma henkin_language_inclusion_chain_map {i} {L : Language} : henkin_language_inclusion = henkin_language_chain_maps L i (i + 1) (by simp[nat.le_succ]) :=
begin
  unfold henkin_language_chain_maps, have : i ≠ i + 1, by {induction i, tidy},
  simp[this], rw[@Lhom.id_is_right_identity ((@henkin_language_chain L).obj i)]
end

def L_infty (L) : Language :=
   colimit_language $ @henkin_language_chain L

/-- For every n : ℕ, return the canonical inclusion L_n → L_infty  --/
def henkin_language_canonical_map {L : Language} (m : ℕ) : (@henkin_language_chain L).obj m →ᴸ (@L_infty L) := by apply canonical_map_language

lemma henkin_language_canonical_map_inj {L : Language} (m : ℕ) : Lhom.is_injective $ @henkin_language_canonical_map L m :=
begin
  split,
  
  {intro n, unfold henkin_language_canonical_map canonical_map_language Lhom.on_function,
  have := @canonical_map_inj_of_transition_maps_inj directed_type_of_nat (@diagram_functions directed_type_of_nat (@henkin_language_chain L) n), unfold canonical_map at this, apply this,intros i j H, dsimp[diagram_functions, henkin_language_chain],
  fapply ((henkin_language_chain_maps_inj) L i j H).on_function},

  {intro n, unfold henkin_language_canonical_map canonical_map_language Lhom.on_relation,
  have := @canonical_map_inj_of_transition_maps_inj directed_type_of_nat (@diagram_relations directed_type_of_nat (@henkin_language_chain L) n), unfold canonical_map at this, apply this,intros i j H, dsimp[diagram_relations, henkin_language_chain],
  fapply ((henkin_language_chain_maps_inj) L i j H).on_relation}
end

/- To prove that T_infty is Henkin, we'll have to exhibit a witnessing function of the form
  wit : bounded_formula 1 → L_infty.constants.

  To do this, we have to recursively go through formulas and terms and show that for every
  formula, there exists some N such that all the symbols in that formula were contained in L_N,
  and therefore, the wit function for L_N introduces the constant we want.

  The natural way to proceed is to define the induced colimit on bounded_formulas, etc.

  Then, we can define the required wit function by taking a bounded formula, picking a
  representative from stage N, applying the wit function from stage N to get something in
  stage N+1, and then pushing it up to L_infty. -/

/- In what follows, "l" is always pre(whatever) level, "k" is always chain index,
   and "n" is always the bound in bounded_(whatever)-/

def henkin_term_chain {L : Language} (l : ℕ) : directed_diagram ℕ' :=
begin
  refine ⟨λ k, preterm (@henkin_language_chain_objects L k) l, _, _⟩,
  {intros x y H, apply Lhom.on_term, apply @henkin_language_chain_maps L, exact H},
  {intros x y z f1 f2 f3, dsimp only [*],
   have : (henkin_language_chain_maps L x z f3) =
   (henkin_language_chain_maps L y z f2) ∘ (henkin_language_chain_maps L x y f1),
   fapply henkin_language_chain.h_mor, rw[this, Lhom.comp_on_term], exact l}
end

def henkin_formula_chain {L : Language} (l : ℕ) : directed_diagram ℕ' :=
begin
  refine ⟨λ k, preformula (@henkin_language_chain_objects L k) l, _, _⟩,
  {intros x y H, apply Lhom.on_formula, apply @henkin_language_chain_maps L, exact H},
  {intros x y z f1 f2 f3, dsimp only [*],
   have : (henkin_language_chain_maps L x z f3) =
   (henkin_language_chain_maps L y z f2) ∘ (henkin_language_chain_maps L x y f1),
   fapply henkin_language_chain.h_mor, rw[this, Lhom.comp_on_formula], exact l}
end

def henkin_bounded_term_chain {L : Language} (n l : ℕ) : directed_diagram ℕ' :=
begin
  refine ⟨λ k, bounded_preterm (@henkin_language_chain_objects L k) n l, _, _⟩,
  {intros x y H, apply Lhom.on_bounded_term, apply @henkin_language_chain_maps L, exact H},
  {intros x y z f1 f2 f3, dsimp only [*],
   have : (henkin_language_chain_maps L x z f3) =
   (henkin_language_chain_maps L y z f2) ∘ (henkin_language_chain_maps L x y f1),
   fapply henkin_language_chain.h_mor, rw[this, Lhom.comp_on_bounded_term]}
end

@[reducible] def henkin_bounded_term_chain' {L : Language} : directed_diagram ℕ' := @henkin_bounded_term_chain L 1 0

def henkin_bounded_formula_chain {L : Language} (n l : ℕ) : directed_diagram ℕ' :=
begin
  refine ⟨λ k, bounded_preformula (@henkin_language_chain_objects L k) n l, _, _⟩,
  {intros x y H, apply Lhom.on_bounded_formula, apply @henkin_language_chain_maps L, exact H},
  {intros x y z f1 f2 f3, dsimp only [*],
   have : (henkin_language_chain_maps L x z f3) =
   (henkin_language_chain_maps L y z f2) ∘ (henkin_language_chain_maps L x y f1),
   fapply henkin_language_chain.h_mor, rw[this, Lhom.comp_on_bounded_formula]}
end

@[reducible]def henkin_bounded_formula_chain' {L : Language} : directed_diagram ℕ' := @henkin_bounded_formula_chain L 1 0

/- L_infty := colim L_n is naturally a cocone over the diagram of languages -/
def cocone_of_L_infty {L : Language} : cocone_language (@henkin_language_chain L) :=
  by apply cocone_of_colimit_language

def cocone_of_term_L_infty {L : Language } (l : ℕ) : cocone (@henkin_term_chain L l) :=
begin
  refine ⟨preterm (L_infty L) l,_,_⟩,
  {intro i, fapply Lhom.on_term, fapply henkin_language_canonical_map},
  {intros i j H, dsimp[henkin_term_chain],
  rw[<-Lhom.comp_on_term],
  have : henkin_language_canonical_map i = (henkin_language_canonical_map j ∘ henkin_language_chain_maps L i j H), swap, rw[this],
  {have := (@cocone_of_L_infty L).h_compat, tidy}, exact l}
end

def cocone_of_formula_L_infty {L : Language } (l : ℕ) : cocone (@henkin_formula_chain L l) :=
begin
  refine ⟨preformula (L_infty L) l,_,_⟩,
  {intro i, fapply Lhom.on_formula, fapply henkin_language_canonical_map},
  {intros i j H, dsimp[henkin_formula_chain],
  rw[<-Lhom.comp_on_formula],
  have : henkin_language_canonical_map i = (henkin_language_canonical_map j ∘ henkin_language_chain_maps L i j H), swap, rw[this],
  {have := (@cocone_of_L_infty L).h_compat, tidy}, exact l}
end

def cocone_of_bounded_term_L_infty {L : Language } (n l : ℕ) : cocone (@henkin_bounded_term_chain L n l) :=
begin
  refine ⟨bounded_preterm (L_infty L) n l,_,_⟩,
  {intro i, fapply Lhom.on_bounded_term, fapply henkin_language_canonical_map},
  {intros i j H, dsimp[henkin_bounded_term_chain],
  rw[<-Lhom.comp_on_bounded_term],
  have : henkin_language_canonical_map i = (henkin_language_canonical_map j ∘ henkin_language_chain_maps L i j H), swap, rw[this],
  {have := (@cocone_of_L_infty L).h_compat, tidy}}
end

def cocone_of_bounded_formula_L_infty {L : Language } (n l : ℕ) : cocone (@henkin_bounded_formula_chain L n l) :=
begin
  refine ⟨bounded_preformula (L_infty L) n l,_,_⟩,
  {intro i, fapply Lhom.on_bounded_formula, fapply henkin_language_canonical_map},
  {intros i j H, dsimp[henkin_bounded_formula_chain],
  rw[<-Lhom.comp_on_bounded_formula],
  have : henkin_language_canonical_map i = (henkin_language_canonical_map j ∘ henkin_language_chain_maps L i j H), swap, rw[this],
  {have := (@cocone_of_L_infty L).h_compat, tidy}}
end

/- bounded_formula (L_infty L) 1 is naturally a cocone over the diagram of bounded_formulas -/
def cocone_of_bounded_formula'_L_infty {L : Language} : cocone (@henkin_bounded_formula_chain' L) :=
begin
  refine ⟨bounded_formula (L_infty L) 1,_,_⟩,
  {intro i, fapply Lhom.on_bounded_formula, fapply henkin_language_canonical_map},
  {intros i j H, dsimp[henkin_bounded_formula_chain', henkin_bounded_formula_chain],
  rw[<-Lhom.comp_on_bounded_formula],
  have : henkin_language_canonical_map i = (henkin_language_canonical_map j ∘ henkin_language_chain_maps L i j H), swap, rw[this],
  {have := (@cocone_of_L_infty L).h_compat, tidy}}
end

def term_comparison {L : Language} (l) : colimit (@henkin_term_chain L l) → preterm (L_infty L) l :=
begin
  change colimit (@henkin_term_chain L l)  → (@cocone_of_term_L_infty L l).vertex,
  apply colimit.universal_map
end

def formula_comparison {L : Language} (l) : colimit (@henkin_formula_chain L l) → preformula (L_infty L) l :=
begin
  change colimit (@henkin_formula_chain L l)  → (@cocone_of_formula_L_infty L l).vertex,
  apply colimit.universal_map
end

def bounded_term_comparison {L : Language} (n l) : colimit (@henkin_bounded_term_chain L n l) → bounded_preterm (L_infty L) n l :=
begin
  change colimit (@henkin_bounded_term_chain L n l)  → (@cocone_of_bounded_term_L_infty L n l).vertex,
  apply colimit.universal_map
end

@[reducible]def bounded_term'_comparison {L : Language}  : colimit (@henkin_bounded_term_chain' L) → bounded_term (L_infty L) 1 := @bounded_term_comparison L 1 0

def bounded_formula_comparison {L : Language} (n l) : colimit (@henkin_bounded_formula_chain L n l) → bounded_preformula (L_infty L) n l :=
begin
  change colimit (@henkin_bounded_formula_chain L n l)  → (@cocone_of_bounded_formula_L_infty L n l).vertex,
  apply colimit.universal_map
end

@[reducible]def bounded_formula'_comparison {L : Language} : colimit (@henkin_bounded_formula_chain' L) → bounded_formula (L_infty L) 1 := @bounded_formula_comparison L 1 0

-- to proceed, need to show that bounded_formula_comparison, as we've defined it,
-- commutes with operations on bounded formulas -- so we need to generalize from
-- bounded_formula 1 to bounded_formula n, and prove colimit statements for terms, etc
-- to complete the structural recursion

/- The universal map from colimit preterm L_n → preterm L_infty is a bijection -/
-- TODO(jesse) refactor with new colimit lemmas
lemma term_comparison_bijective {L : Language} (l) : function.bijective (@term_comparison L l) :=
begin
  refine ⟨_,_⟩,
  {{unfold term_comparison id, fapply universal_map_inj_of_components_inj,
  change ∀ i : ℕ, function.injective ((cocone_of_term_L_infty l).map i),
  dsimp[cocone_of_term_L_infty],  intro m,
  fapply Lhom.on_term_inj (@henkin_language_canonical_map_inj L m)},},
  {intro f, induction f,
    {refine ⟨(by {fapply canonical_map, by {change ℕ, exact 0}, exact var f}), by split⟩},
    {have W := germ_rep f_f, rcases W with ⟨⟨i,x⟩, Hx⟩, fapply exists.intro, 
     fapply canonical_map i, fapply func, exact x, rw[<-Hx], refl},
    {rcases f_ih_t with ⟨t, Ht⟩, rcases f_ih_s with ⟨s,Hs⟩, have Wt := germ_rep t,
    have Ws := germ_rep s, rcases Wt with ⟨⟨i,x_t⟩, Hxt⟩, rcases Ws with ⟨⟨j, x_s⟩, Hxs⟩,
    let x_t' : (henkin_term_chain (f_l + 1)).obj (i+j),
      fapply (henkin_term_chain (f_l + 1)).mor, exact i,
      simp only [ℕ', directed_type.rel, id.def, zero_le, le_add_iff_nonneg_right],
      exact x_t,
    let x_s' : (henkin_term_chain 0).obj (i+j),
      fapply (henkin_term_chain 0).mor, exact j,
      simp only [ℕ', directed_type.rel, zero_le, le_add_iff_nonneg_left],
      exact x_s,
    have Hxt' : ⟦(⟨i+j,x_t'⟩ : coproduct_of_directed_diagram $ henkin_term_chain (f_l + 1))⟧ = t,
      {rw[<-Hxt], simp[(≈), germ_relation], refine ⟨(i+j),x_t',⟨by simp,_⟩,_⟩,
       dsimp[henkin_term_chain, henkin_language_chain_maps], let k := i + j,
       simp only [id_of_self_map], apply Lhom.id_term,
       fapply exists.intro, simp only [zero_le, le_add_iff_nonneg_right]},
    have Hxs' : ⟦(⟨i+j,x_s'⟩ : coproduct_of_directed_diagram $ henkin_term_chain 0)⟧ = s,
    {{rw[<-Hxs], simp[(≈), germ_relation], refine ⟨(i+j),x_s',⟨by simp,_⟩,_⟩,
       dsimp[henkin_term_chain, henkin_language_chain_maps], let k := i + j,
       simp only [id_of_self_map], apply Lhom.id_term,
       fapply exists.intro, simp only [zero_le, le_add_iff_nonneg_left]},},   
    fapply exists.intro, fapply canonical_map, change ℕ, exact (i + j),
    fapply app, exact x_t', exact x_s', rw[<-Ht, <-Hs, <-Hxt', <-Hxs'], refl},}
end

/- At some point, I should write out explicitly the fact that all the comparison maps
   structurally recurse -/
lemma formula_comparison_bijective {L : Language} (l) : function.bijective (@formula_comparison L l) :=
begin
  refine ⟨_,_⟩,
  {{unfold formula_comparison id, fapply universal_map_inj_of_components_inj,
  change ∀ i : ℕ, function.injective ((cocone_of_formula_L_infty l).map i),
  dsimp[cocone_of_formula_L_infty],  intro m,
  fapply Lhom.on_formula_inj (@henkin_language_canonical_map_inj L m)},},
  {intro f, induction f,
  {refine ⟨(by {fapply canonical_map, by {change ℕ, exact 0}, exact falsum}), by split⟩},
  {
    rcases (term_comparison_bijective 0).right f_t₁ with ⟨t₁, H₁⟩, rcases (term_comparison_bijective 0).right f_t₂ with ⟨t₂, H₂⟩,
    rcases germ_rep t₁ with ⟨⟨i,x⟩,Hx⟩, rcases germ_rep t₂ with ⟨⟨j,y⟩,Hy⟩,
    fapply exists.intro, fapply canonical_map, exact i+j, fapply equal,
    exact push_to_sum_r x j, exact push_to_sum_l y i,
    rw[<-H₁, <-H₂,<-Hx, <-Hy, <-canonical_map_quotient, same_fiber_as_push_to_r x j ,<-canonical_map_quotient, same_fiber_as_push_to_l y i],
    simpa only},
  {have x := germ_rep f_R, rcases x with ⟨⟨i,x⟩,H⟩, fapply exists.intro, have R' := rel x,
   exact ⟦⟨i,R'⟩⟧, tidy},
  {rcases (psigma_of_exists f_ih) with ⟨t₁, H₁⟩,
   rcases (term_comparison_bijective 0).right f_t with ⟨t₂, H₂⟩,
   rcases germ_rep t₁ with ⟨⟨i,x⟩,Hx⟩, rcases germ_rep t₂ with ⟨⟨j,y⟩,Hy⟩,
   fapply exists.intro, fapply canonical_map, exact i+j, fapply apprel,
   exact push_to_sum_r x j, exact push_to_sum_l y i,
    rw[<-H₁, <-H₂,<-Hx, <-Hy, <-canonical_map_quotient, same_fiber_as_push_to_r x j ,<-canonical_map_quotient, same_fiber_as_push_to_l y i],
    simpa only},
  {rcases (psigma_of_exists f_ih_f₁) with ⟨t₁, H₁⟩,
    rcases (psigma_of_exists f_ih_f₂) with ⟨t₂, H₂⟩,
   rcases germ_rep t₁ with ⟨⟨i,x⟩,Hx⟩, rcases germ_rep t₂ with ⟨⟨j,y⟩,Hy⟩,
   fapply exists.intro, fapply canonical_map, exact (i+j), fapply imp,
   exact push_to_sum_r x j, exact push_to_sum_l y i,
    rw[<-H₁, <-H₂,<-Hx, <-Hy, <-canonical_map_quotient, same_fiber_as_push_to_r x j ,<-canonical_map_quotient, same_fiber_as_push_to_l y i],
    simpa only},
  {rcases (psigma_of_exists f_ih) with ⟨t₁, H₁⟩,
   rcases germ_rep t₁ with ⟨⟨i,x⟩,Hx⟩,
   fapply exists.intro, fapply canonical_map, exact i, fapply all,
   exact x, rw[<-H₁, <-Hx], simpa only}}
end

@[simp]lemma bounded_term_comparison_bijective {L : Language} (n l) : function.bijective (@bounded_term_comparison L n l) :=
begin
refine ⟨_,_⟩,
  {{unfold bounded_term_comparison id, fapply universal_map_inj_of_components_inj,
  change ∀ i : ℕ, function.injective ((cocone_of_bounded_term_L_infty n l).map i),
  dsimp[cocone_of_bounded_term_L_infty],  intro m,
  fapply Lhom.on_bounded_term_inj (@henkin_language_canonical_map_inj L m)},},
   {intro f, induction f,
    {refine ⟨(by {fapply canonical_map, by {change ℕ, exact 0}, exact bd_var f}), by split⟩},
    {have W := germ_rep f_f, rcases W with ⟨⟨i,x⟩, Hx⟩, fapply exists.intro, 
     fapply canonical_map i, fapply bd_func, exact x, rw[<-Hx], refl,},
    {rcases f_ih_t with ⟨t, Ht⟩, rcases f_ih_s with ⟨s,Hs⟩, have Wt := germ_rep t,
    have Ws := germ_rep s, rcases Wt with ⟨⟨i,x_t⟩, Hxt⟩, rcases Ws with ⟨⟨j, x_s⟩, Hxs⟩,
    let x_t' : (henkin_bounded_term_chain n (f_l + 1)).obj (i+j),
      fapply (henkin_bounded_term_chain n (f_l + 1)).mor, exact i,
      simp only [ℕ', directed_type.rel, id.def, zero_le, le_add_iff_nonneg_right],
      exact x_t,
    let x_s' : (henkin_bounded_term_chain n 0).obj (i+j),
      fapply (henkin_bounded_term_chain n 0).mor, exact j,
      simp only [ℕ', directed_type.rel, zero_le, le_add_iff_nonneg_left],
      exact x_s,
    have Hxt' : ⟦(⟨i+j,x_t'⟩ : coproduct_of_directed_diagram $ henkin_bounded_term_chain n (f_l + 1))⟧ = t,
      {rw[<-Hxt], simp[(≈), germ_relation], refine ⟨(i+j),x_t',⟨by simp,_⟩,_⟩,
       dsimp[henkin_bounded_term_chain, henkin_language_chain_maps], let k := i + j,
       simp only [id_of_self_map], apply Lhom.id_bounded_term,
       fapply exists.intro, simp only [zero_le, le_add_iff_nonneg_right]},
    have Hxs' : ⟦(⟨i+j,x_s'⟩ : coproduct_of_directed_diagram $ henkin_bounded_term_chain n 0)⟧ = s,
    {{rw[<-Hxs], simp[(≈), germ_relation], refine ⟨(i+j),x_s',⟨by simp,_⟩,_⟩,
       dsimp[henkin_bounded_term_chain, henkin_language_chain_maps], let k := i + j,
       simp only [id_of_self_map], apply Lhom.id_bounded_term,
       fapply exists.intro, simp only [zero_le, le_add_iff_nonneg_left]},},   
    fapply exists.intro, fapply canonical_map, change ℕ, exact (i + j),
    fapply bd_app, exact x_t', exact x_s', rw[<-Ht, <-Hs, <-Hxt', <-Hxs'], refl},}
end

@[simp]lemma bounded_formula_comparison_bijective {L : Language} (n l) : function.bijective (@bounded_formula_comparison L n l) :=
begin
refine ⟨_,_⟩,
  {{unfold bounded_formula_comparison id, fapply universal_map_inj_of_components_inj,
  change ∀ i : ℕ, function.injective ((cocone_of_bounded_formula_L_infty n l).map i),
  dsimp[cocone_of_bounded_formula_L_infty],  intro m,
  fapply Lhom.on_bounded_formula_inj (@henkin_language_canonical_map_inj L m)},},
  {intro f, induction f,
  {refine ⟨(by {fapply canonical_map, by {change ℕ, exact 0}, exact bd_falsum}), by split⟩},
  { 
    rcases (bounded_term_comparison_bijective f_n 0).right f_t₁ with ⟨t₁, H₁⟩, rcases (bounded_term_comparison_bijective f_n 0).right f_t₂ with ⟨t₂, H₂⟩,
    rcases germ_rep t₁ with ⟨⟨i,x⟩,Hx⟩, rcases germ_rep t₂ with ⟨⟨j,y⟩,Hy⟩,
    fapply exists.intro, fapply canonical_map, exact i+j, fapply bd_equal,
    exact push_to_sum_r x j, exact push_to_sum_l y i,
    simp[H₁, H₂], 
    rw[<-H₁, <-H₂,<-Hx, <-Hy, <-canonical_map_quotient, same_fiber_as_push_to_r x j ,<-canonical_map_quotient, same_fiber_as_push_to_l y i],
    simpa only},
  {have x := germ_rep f_R, rcases x with ⟨⟨i,x⟩,H⟩, fapply exists.intro, have R' := bd_rel x,
   exact ⟦⟨i,R'⟩⟧, tidy},
  {rcases (psigma_of_exists f_ih) with ⟨t₁, H₁⟩,
   rcases (bounded_term_comparison_bijective _ 0).right f_t with ⟨t₂, H₂⟩,
   rcases germ_rep t₁ with ⟨⟨i,x⟩,Hx⟩, rcases germ_rep t₂ with ⟨⟨j,y⟩,Hy⟩,
   fapply exists.intro, fapply canonical_map, exact i+j, fapply bd_apprel,
   exact push_to_sum_r x j, exact push_to_sum_l y i,
    rw[<-H₁, <-H₂,<-Hx, <-Hy, <-canonical_map_quotient, same_fiber_as_push_to_r x j ,<-canonical_map_quotient, same_fiber_as_push_to_l y i],
    simpa only},
  {rcases (psigma_of_exists f_ih_f₁) with ⟨t₁, H₁⟩,
    rcases (psigma_of_exists f_ih_f₂) with ⟨t₂, H₂⟩,
   rcases germ_rep t₁ with ⟨⟨i,x⟩,Hx⟩, rcases germ_rep t₂ with ⟨⟨j,y⟩,Hy⟩,
   fapply exists.intro, fapply canonical_map, exact (i+j), fapply bd_imp,
   exact push_to_sum_r x j, exact push_to_sum_l y i,
    rw[<-H₁, <-H₂,<-Hx, <-Hy, <-canonical_map_quotient, same_fiber_as_push_to_r x j ,<-canonical_map_quotient, same_fiber_as_push_to_l y i],
    simpa only},
  {rcases (psigma_of_exists f_ih) with ⟨t₁, H₁⟩,
   rcases germ_rep t₁ with ⟨⟨i,x⟩,Hx⟩,
   fapply exists.intro, fapply canonical_map, exact i, fapply bd_all,
   exact x, rw[<-H₁, <-Hx], simpa only}},
end

@[simp]lemma bounded_formula'_comparison_bijective {L : Language} : function.bijective (@bounded_formula'_comparison L) :=
by apply bounded_formula_comparison_bijective 

noncomputable def equiv_bounded_formula_comparison {L : Language} : equiv (colimit (@henkin_bounded_formula_chain' L)) (bounded_formula (L_infty L) 1) :=
begin fapply equiv.of_bijective, exacts [bounded_formula'_comparison, bounded_formula'_comparison_bijective] end

/- Not really a chain, since we haven't set up interpretations of theories yet -/
def henkin_theory_chain {L : Language} {T : Theory L}: Π(n : ℕ), (Theory (obj (@henkin_language_chain L) n))
| 0 := T
| (n+1) := henkin_theory_step (henkin_theory_chain n)

/- Now we have to push all these theories into Theory L_∞, so that they literally become a chain
   of sets. -/

/- Given T_n from henkin_theory_chain, ι T_n is the expansion of T_n to an L_infty theory -/
def ι {L : Language} {T : Theory L} (m : ℕ) :  Theory (L_infty L) :=
(Lhom.on_sentence (@henkin_language_canonical_map L m)) '' (@henkin_theory_chain L T m)

@[simp]lemma in_iota_of_in_step {L} (i) {T} (f : sentence (@henkin_language_chain_objects L (i+1))): f ∈ (@henkin_theory_chain L T (i+1)) →  Lhom.on_bounded_formula (@henkin_language_canonical_map L (i + 1)) f ∈ @ι L T (i + 1) :=
  by {intro H, split, swap, exact f, refine ⟨H,_⟩, refl}

/- T_infty is the henkinization of T; we define it to be the union ⋃ (n : ℕ), ι(T n). -/
def T_infty {L : Language} (T : Theory L) : Theory (L_infty L) := set.Union (@ι L T)

def henkin_language {L} {T : Theory L} {hT : is_consistent T} : Language := L_infty L

local infix ` →ᴸ `:10 := Lhom -- \^L

/- I dislike this proof, but I don't know how apply canonical_map_language otherwise... -/
def henkin_language_over {L} {T : Theory L} {hT : is_consistent T} : L →ᴸ (@henkin_language L T hT) :=
by {change (henkin_language_chain.obj (0 : ℕ)) →ᴸ colimit_language henkin_language_chain, apply canonical_map_language}

lemma henkin_language_over_injective {L} {T : Theory L} {hT : is_consistent T} : Lhom.is_injective (@henkin_language_over L T hT) :=
begin
  split, all_goals{intro n, unfold henkin_language_over canonical_map_language, simp,
  rw[<-canonical_map], fapply canonical_map_inj_of_transition_maps_inj, intros i j H,
  dsimp[diagram_functions, diagram_relations, henkin_language_chain],
  simp only [henkin_language_chain_maps_inj, Lhom.is_injective.on_function, Lhom.is_injective.on_relation]}
end

def complete_henkin_Theory_over {L : Language} (T : Theory L) (hT : is_consistent T) : Type u := Σ' T' : Theory_over T hT, has_enough_constants T'.val ∧ is_complete T'.val

def henkinization {L : Language} {T : Theory L} (hT : is_consistent T) : Theory (@henkin_language L T hT) := T_infty T

/-- Given an f : bounded_formula L_infty, return a Henkin witness for f, along with all the
    data and conditions needed to obtain this witness --/
noncomputable def wit_infty {L} {T : Theory L} {hT : is_consistent T} (f : bounded_formula (@henkin_language L T hT) 1) : Σ c : (@henkin_language L T hT).constants, Σ (f' : Σ' (x : colimit (@henkin_bounded_formula_chain' L)), bounded_formula'_comparison x = f), Σ' (f'' : coproduct_of_directed_diagram (@henkin_bounded_formula_chain' L)), ⟦f''⟧ = f'.fst ∧ c = (henkin_language_canonical_map (f''.fst + 1)).on_function  (wit' f''.snd) :=
begin
  have f_lift1 := psigma_of_exists ((bounded_formula'_comparison_bijective).right f),
  have f_lift2 := germ_rep (f_lift1.fst),
  refine ⟨(henkin_language_canonical_map (f_lift2.fst.fst + 1)).on_function (wit' (f_lift2.fst.snd)), f_lift1,(f_lift2.fst), f_lift2.snd,rfl⟩,
end

lemma henkinization_is_henkin {L : Language} {T : Theory L} (hT : is_consistent T) : has_enough_constants (henkinization hT) :=
begin
  apply has_enough_constants.intro,
  unfold henkinization T_infty, intro f, have big_sigma := wit_infty f, rcases big_sigma with ⟨c, blah⟩, refine ⟨c,_⟩,
  rcases blah with ⟨⟨f', Hf'⟩,⟨i, f''⟩, H⟩,
  fapply nonempty.intro, fapply axm,
  simp only [*, fol.subst_formula, fol.bounded_preterm.fst, set.mem_Union, set.mem_image, fol.subst0_bounded_formula_fst, fol.bounded_preformula.fst],
  refine ⟨_,⟨(i+1),_⟩,_⟩,
  {fapply Lhom.on_bounded_formula, exact (@henkin_language_chain L).obj (i+1),
   fapply henkin_language_canonical_map, fapply wit_property, fapply Lhom.on_bounded_formula,
   exact (@henkin_language_chain L).obj i, exact henkin_language_inclusion,
   exact f'', exact (wit' f'')},
  {fapply in_iota_of_in_step, fapply or.inr, tidy},
  {let c_infty := (bd_const ((henkin_language_canonical_map (i + 1)).on_function (wit' f''))),
  have this1 : bounded_preformula.fst (∃' f) ⟹
      (bounded_preformula.fst f)[bounded_preterm.fst
          (bd_const ((henkin_language_canonical_map (i + 1)).on_function (wit' f''))) //
        0] = bounded_preformula.fst ((∃' f) ⟹ f[c_infty/0]), by simp, rw[this1],
  suffices : (Lhom.on_bounded_formula (henkin_language_canonical_map (i + 1))
         (wit_property (Lhom.on_bounded_formula henkin_language_inclusion f'') (wit' f''))) = (∃' f ⟹ f[c_infty /0]), by rw[this], 
  unfold wit_property at *, dsimp[c_infty], rw[<-canonical_map_quotient] at H, dsimp at H,
  rw[<-Hf',<-H.left],
  unfold bounded_formula'_comparison bounded_formula_comparison id, 
  rw[(@universal_map_property ℕ' (henkin_bounded_formula_chain') (cocone_of_bounded_formula'_L_infty) i f'')],
  dsimp[cocone_of_bounded_formula'_L_infty],
  have : henkin_language_canonical_map i = henkin_language_canonical_map (i+1) ∘ henkin_language_inclusion,
    {have := cocone_of_L_infty.h_compat, have a := @this i (i+1) (by simp),
     dsimp[cocone_of_L_infty, cocone_of_colimit_language, henkin_language_chain] at a,
     unfold henkin_language_canonical_map, simp only [*, henkin_language_inclusion_chain_map],
     exact a},
  rw[this,Lhom.comp_on_bounded_formula],
  have : (function.comp (Lhom.on_bounded_formula (henkin_language_canonical_map (i + 1)))
           (Lhom.on_bounded_formula henkin_language_inclusion) f'') = Lhom.on_bounded_formula (henkin_language_canonical_map (i+1)) (Lhom.on_bounded_formula henkin_language_inclusion f''),
       by refl,
  rw[this],
  have : (Lhom.on_bounded_formula (henkin_language_canonical_map (i + 1))
           (Lhom.on_bounded_formula henkin_language_inclusion f''))[bd_const
          ((henkin_language_canonical_map (i + 1)).on_function (wit' f'')) /0] = 
          (Lhom.on_bounded_formula (henkin_language_canonical_map (i + 1))
           ((Lhom.on_bounded_formula henkin_language_inclusion f'')[bd_const
           (wit' f'') /0])), 
  by tidy, rw[this],
  have : ∃' Lhom.on_bounded_formula (henkin_language_canonical_map (i + 1))
          (Lhom.on_bounded_formula henkin_language_inclusion f'')
          = Lhom.on_bounded_formula (henkin_language_canonical_map (i+1)) (∃' (Lhom.on_bounded_formula henkin_language_inclusion f'')),
  by tidy, rw[this]}
end

lemma is_consistent_henkinization {L : Language} {T : Theory L} (hT : is_consistent T) : is_consistent (henkinization hT) :=
begin
  intro P, have := proof_compactness P,
  have : ∃ k : ℕ, Theory.fst (@ι L T k) ⊢' (bd_falsum).fst,
    by {sorry}, -- again, this depends on picking a representative of a germ-eq class
                -- on the induced colimit of formulas
  cases this with k P', unfold ι at P',
  let T' := henkin_theory_chain k,
  have : is_consistent T', by {sorry}, -- now we need to prove that finitely many steps preserve consistency
  have : T' ⊢' (bd_falsum), swap, contradiction,
  fapply nonempty.intro, fapply Lhom.reflect_prf, exact L_infty L,
  exact henkin_language_canonical_map k,
  fapply henkin_language_canonical_map_inj,
  simp only [*, fol.Lhom.on_formula, fol.bounded_preformula.fst],
  {sorry}, -- need to prove Theory.fst ∘ on_sentence  = on_formulas ∘ Theory.fst
  repeat{assumption}
end

noncomputable def complete_henkinization {L} {T : Theory L} (hT : is_consistent T) := completion_of_consis _ (henkinization hT) (is_consistent_henkinization hT)

/- Bundled versions below -/
def Language_over (L : Language) := Σ L' : Language, L →ᴸ L'

def henkin_Theory_over {L : Language} (T : Theory L) (hT : is_consistent T) : Type u := Σ' T' : Theory_over T hT, has_enough_constants T'.val
/-- Given an L-theory T, return a larger language L' and a Henkin theory T' extending T viewed as an L'-theory --/
def henkinization' {L : Language} {T : Theory L} (hT : is_consistent T) : Σ (L' : Language_over L), henkin_Theory_over (Theory_induced L'.snd T) begin apply consis_Theory_induced_of_consis, repeat{assumption} end := sorry

/-- The completion of a Henkin theory is again Henkin. --/
lemma has_enough_constants_of_completion {L} {T : Theory L} (hT : is_consistent T) : is_consistent (completion_of_consis _ (@henkinization L T hT) (is_consistent_henkinization hT)).fst.val := sorry

/-- Given an L-theory T, return a completed Henkinization of T --/
def complete_henkinization' {L : Language} {T : Theory L} (hT : is_consistent T) : Σ (L' : Language_over L), complete_henkin_Theory_over (Theory_induced L'.snd T) begin apply consis_Theory_induced_of_consis, repeat{assumption} end := sorry
