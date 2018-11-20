import .fol order.zorn order.filter logic.basic data.finset data.set tactic.tidy .completion .language_extension

local attribute [instance, priority 0] classical.prop_decidable

open fol

-- #check language_morphism

def henkin_Theory_over {L : Language} (T : Theory L) (hT : is_consistent T) : Type := Σ' T' : Theory_over T hT, has_enough_constants T'.val

/-- Given an L-theory T, return a larger language L' and a Henkin theory T' extending T viewed as an L'-theory --/
def henkinization {L : Language} {T : Theory L} (hT : is_consistent T) : Σ (L' : Language_over L), henkin_Theory_over (Theory_induced L'.snd T) begin apply consis_Theory_induced_of_consis, repeat{assumption} end := sorry

/-- The completion of a Henkin theory is again Henkin. --/
lemma has_enough_constants_of_completed 
