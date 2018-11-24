import .fol order.zorn order.filter logic.basic data.finset data.set tactic.tidy .completion .language_extension .colimit

local attribute [instance, priority 0] classical.prop_decidable

open fol

universes u v
local infix ` →ᴸ `:10 := Lhom -- \^L

/- Temporarily putting this here because I can't get Lean to recognize Lhom in colimit.lean -/
namespace colimit
#print directed_diagram

export directed_type

/- Below we define colimits of languages. These are just fieldwise (and then indexwise)
   colimits of types, so the proofs are very similar. -/
@[reducible]def Lhom_comp {L1} {L2} {L3} (g : L2 →ᴸ L3) (f : L1 →ᴸ L2) : L1 →ᴸ L3 :=
begin
--  rcases g with ⟨g1, g2⟩, rcases f with ⟨f1,f2⟩,
--  exact ⟨λn, g1 ∘ f1, λn, g2 ∘ f2⟩
split, 
  all_goals{intro n},
  let g1 := g.on_function, let f1 := f.on_function,-- Lean's not letting me "@" g.on_function etc
    exact (@g1 n) ∘ (@f1 n),
  let g2 := g.on_relation, let f2 := f.on_relation,
    exact (@g2 n) ∘ (@f2 n)
end 

local infix ` ∘ `:60 := Lhom_comp

/- on_function and on_relation are functors to Type* -/
lemma Lhom_comp_on_function {L1} {L2} {L3} (g : L2 →ᴸ L3) (f : L1 →ᴸ L2) :
      (g ∘ f).on_function =
      begin intro n, let g1 := g.on_function, let f1 := f.on_function,
      exact function.comp (@g1 n) (@f1 n) end
      := by refl

lemma Lhom_comp_on_relation {L1} {L2} {L3} (g : L2 →ᴸ L3) (f : L1 →ᴸ L2) :
      (g ∘ f).on_relation =
      begin intro n, let g1 := g.on_relation, let f1 := f.on_relation,
      exact function.comp (@g1 n) (@f1 n) end
      := by refl

structure directed_diagram_language (D : (directed_type.{u})) : Type (max (u+1) (v+1)) :=
  (obj : D.carrier → (Language.{v}))
  (mor : ∀{x}, ∀{y}, D.rel x y → (obj x →ᴸ obj y))
  (h_mor : ∀{x} {y} {z} {f1 : D.rel x y} {f2 : D.rel y z} {f3 : D.rel x z},
            (mor f3) = (mor f2) ∘ (mor f1)) -- functoriality

export directed_diagram_language

/- Given a directed diagram of languages, we obtain two ℕ-indexed families of
   directed diagrams of types: one by restricting to functions and one by
   restricting to relations. -/
def diagram_functions {D : (directed_type)} {F : (directed_diagram_language D)} (n : ℕ) :
                      ((directed_diagram D)) :=
begin
  refine ⟨by {intro x, exact (obj F x).functions n},_,_⟩,
  {intros x y edge, have := (F.mor edge).on_function, exact @this n},
  {intros, simp only [], have := F.h_mor, have := @this x y z f1 f2 f3, rw[this]},
end

def diagram_relations {D : (directed_type)} {F : (directed_diagram_language D)} (n : ℕ) :
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

/- Given a language, iterate henkin_language_step, returning this data in the form
   of a directed diagram of types indexed by ℕ' -/
def henkin_language_chain {L : (Language : Type(u+1))} : (directed_diagram_language directed_type_of_nat) := 
begin
  refine ⟨_, _, _⟩,
  {intro n, induction n with n ih,
    {exact L}, -- case n = 0
    {exact henkin_language_step ih},
  },
  {sorry},
  {sorry}
end

def complete_henkin_Theory_over {L : Language} (T : Theory L) (hT : is_consistent T) : Type u := Σ' T' : Theory_over T hT, has_enough_constants T'.val ∧ is_complete T'.val

def henkin_language {L} {T : Theory L} {hT : is_consistent T} : Language := sorry

local infix ` →ᴸ `:10 := Lhom -- \^L

lemma henkin_language_over {L} {T : Theory L} {hT : is_consistent T} : L →ᴸ (@henkin_language L T hT) := sorry

def henkinization {L : Language} {T : Theory L} {hT : is_consistent T} : Theory (@henkin_language L T hT) := sorry

lemma henkinization_is_henkin {L : Language} {T : Theory L} {hT : is_consistent T} : has_enough_constants (@henkinization L T hT) := sorry

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
