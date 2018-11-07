import .fol order.zorn order.filter logic.basic data.finset data.set tactic.tidy .completion .language_extension

local attribute [instance, priority 0] classical.prop_decidable

open fol

#check language_morphism

def henkinization {L : Language} {T : Theory L} (hT : is_consistent T) : Σ (L' : Language_over L), Theory_over (Theory_induced L'.snd T) sorry := sorry
