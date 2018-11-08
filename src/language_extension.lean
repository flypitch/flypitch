import .fol

namespace fol

namespace Language
protected def sum (L L' : Language) : Language :=
⟨λn, L.functions n ⊕ L'.functions n, λ n, L.relations n ⊕ L'.relations n⟩
end Language

structure Lhom (L L' : Language) :=
(on_functions : ∀{n}, L.functions n → L'.functions n) 
(on_relations : ∀{n}, L.relations n → L'.relations n)

local infix ` →ᴸ `:10 := Lhom -- \^L

namespace Lhom

variables {L : Language} {L' : Language} (ϕ : L →ᴸ L')

protected def id (L : Language) : L →ᴸ L :=
⟨λn, id, λ n, id⟩

protected def on_terms : ∀{l}, preterm L l → preterm L' l
| _ &k          := &k
| _ (func f)    := func $ ϕ.on_functions f
| _ (app t₁ t₂) := app (on_terms t₁) (on_terms t₂)

protected def on_formulae : ∀{l}, preformula L l → preformula L' l
| _ falsum       := falsum
| _ (t₁ ≃ t₂)    := ϕ.on_terms t₁ ≃ ϕ.on_terms t₂
| _ (rel R)      := rel $ ϕ.on_relations R
| _ (apprel f t) := apprel (on_formulae f) $ ϕ.on_terms t
| _ (f₁ ⟹ f₂)   := on_formulae f₁ ⟹ on_formulae f₂
| _ (∀' f)       := ∀' on_formulae f

end Lhom

end fol

-- def Theory_induced {L L' : Language} (F : language_morphism L L') (T : Theory L) : Theory L' := begin sorry end

-- def Language_over := Σ L' : Language, language_morphism L L'

-- instance nonempty_Language_over : nonempty (Language_over) :=
--   begin fapply nonempty.intro, exact ⟨L, language_id_morphism L⟩ end

--TODO define map induced by a language_morphism on terms/preterms, formulas/preformulas, sets of formulas/theories
