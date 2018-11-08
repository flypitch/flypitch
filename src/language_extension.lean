import .fol order.zorn order.filter logic.basic data.finset data.set tactic.tidy .completion

local attribute [instance, priority 0] classical.prop_decidable

open fol

section language_extension

def language_morphism (L L' : Language) := Π n : ℕ, (L.relations n → L'.relations n) × (L.functions n → L'.functions n)

def language_id_morphism : Π L : Language, language_morphism L L :=
begin
  intro L, intro n, exact ⟨id, id⟩
end

def Theory_induced {L L' : Language} (F : language_morphism L L') (T : Theory L) : Theory L' := begin sorry end

parameter L : Language

def Language_over := Σ L' : Language, language_morphism L L'

instance nonempty_Language_over : nonempty (Language_over) :=
  begin fapply nonempty.intro, exact ⟨L, language_id_morphism L⟩ end

--TODO define map induced by a language_morphism on terms/preterms, formulas/preformulas, sets of formulas/theories

end language_extension
