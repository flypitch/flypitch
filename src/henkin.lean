import .fol order.zorn order.filter logic.basic data.finset data.set tactic.tidy .completion .language_extension

local attribute [instance, priority 0] classical.prop_decidable

open fol

-- #check language_morphism

universe u



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
