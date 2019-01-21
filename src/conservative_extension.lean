import .fol .language_extension .completeness tactic.find

/- A framework for proving things in a smaller theory by working in a conservative expansion -/ 

namespace fol
@[reducible, simp]def conservative {L} {T₁ : Theory L} {T₂ : Theory L} (h : T₁ ⊆ T₂) (f : sentence L) : Prop :=
  T₁ ⊢' f ↔ T₂ ⊢' f
@[reducible, simp]def model_conservative {L} {T₁ : Theory L} {T₂ : Theory L} (h : T₁ ⊆ T₂) (f : sentence L) : Prop :=
  T₁ ⊨ f ↔ T₂ ⊨ f

lemma model_conservative_iff_conservative {L} {T₁ : Theory L} {T₂ : Theory L} (h : T₁ ⊆ T₂) (f : sentence L) : model_conservative h f ↔ conservative h f :=
  by simp[completeness]

end fol

namespace fol
namespace Lhom

section conservativity

notation ϕ`[`:95 T₁`]`:90 := Lhom.Theory_induced ϕ T₁ 
notation ϕ`[`:95 f`]`:90 := Lhom.on_sentence ϕ f

/-- Given an L₁-theory T₁, an L₂-theory T₂ such that h : ϕ[T₁] ⊆ ϕ[T₂], we say that that T₂ is conservative over T₁ at f if h is conservative at ϕ[f]. -/

@[reducible, simp]def conservative {L₁ L₂} (ϕ : L₁ →ᴸ L₂) (T₁ : Theory L₁) (T₂ : Theory L₂) (f : sentence L₁) (h : ϕ[T₁] ⊆ T₂) :=
  fol.conservative h $ ϕ[f]

private lemma conservative_sanity_check {L₁ L₂ : Language} (ϕ : L₁ →ᴸ L₂) (T₁ : Theory L₁) (T₂ : Theory L₂) (f : sentence L₁) (h : ϕ[T₁] ⊆ T₂) :
 conservative ϕ T₁ T₂ f h ↔ ((ϕ[T₁] ⊢' ϕ[f]) ↔ T₂ ⊢' ϕ[f]) := by refl -- phew

/- An L₂-structure M₂ is the expansion along ϕ is an L₁-structure M₁ if M₁ is equal to the ϕ-reduct of M₂. -/  
@[reducible, simp]def is_expansion {L₁ L₂} (ϕ : L₁ →ᴸ L₂) (M₂ : Structure L₂) (M₁ : Structure L₁) := M₁ = M₂[ϕ]

theorem by_conservativity {L₁ L₂} (ϕ : L₁ →ᴸ L₂) (h_ϕ : is_injective ϕ) (M₂ : Structure L₂) (M₁ : Structure L₁)
  (h_expansion : is_expansion ϕ M₂ M₁) 
  (T₁ : Theory L₁) (T₂ : Theory L₂) (f : sentence L₁) (h_M₁ : M₁ ⊨ T₁) (h_M₂ : M₂ ⊨ T₂)
  (h : ϕ[T₁] ⊆ T₂) (h_conservative : conservative ϕ T₁ T₂ f h) (f' : sentence L₂)
  (h_equiv : M₂ ⊨ ϕ[f] ↔ M₂ ⊨ f') :
    M₂ ⊨ f' → M₁ ⊨ f :=
λ H, by {unfold is_expansion at h_expansion, rw[h_expansion],
             apply reduct_ssatisfied h_ϕ, exact h_equiv.mpr H}

end conservativity

-- TODO use typeclasses to handle bookkeeping of hierarchy of expansions of a type?
