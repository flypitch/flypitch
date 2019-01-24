import .fol .language_extension .completeness tactic.find .zfc

local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`:0) := l

/- A framework for proving things in a smaller theory by working in a conservative expansion -/ 

namespace fol
@[reducible, simp]def conservative {L} {T₁ : Theory L} {T₂ : Theory L} (h : T₁ ⊆ T₂) (f : sentence L) : Prop :=
  T₁ ⊢' f ↔ T₂ ⊢' f
@[reducible, simp]def model_conservative {L} {T₁ : Theory L} {T₂ : Theory L} (h : T₁ ⊆ T₂) (f : sentence L) : Prop :=
  T₁ ⊨ f ↔ T₂ ⊨ f

lemma model_conservative_iff_conservative {L} {T₁ : Theory L} {T₂ : Theory L} (h : T₁ ⊆ T₂) (f : sentence L) : model_conservative h f ↔ conservative h f :=
  by simp[completeness]

section const
/- constants are a special case of the lemmas that follow this section -/

@[reducible]def graph_relation_constant {L : Language} (c : L.constants) : bounded_formula L 1 :=
  &0 ≃ (bd_const c)

/- A 1-formula f(x) defines a constant c modulo T if T ⊢' c is the unique solution to f(x) -/
@[reducible]def defines_constant {L} {T : Theory L} (f : bounded_formula L 1) (c : L.constants) :=
T ⊢' ∀'(f ⇔ graph_relation_constant c)

lemma graph_relation_soundness_constant {L : Language} {c : L.constants} {M : Structure L} : ∀ x : M, realize_bounded_formula ([x]) (graph_relation_constant c) ([]) ↔ (x = realize_bounded_term dvector.nil (bd_const c) dvector.nil) := by intro; refl

theorem graph_relation_constant_defines_constant {L} {T : Theory L} {c : L.constants} : @defines_constant _ T (graph_relation_constant c) c :=
by {rw[graph_relation_constant,defines_constant,completeness _ _], intros M h1 h2 a, finish}

theorem defines_constant_elimination {L} {T : Theory L} {c : L.constants} {f : bounded_formula L 1} {Γ : bounded_formula L 1} {h_Γ : @defines_constant _ T Γ c} :
T ⊢' ∀'(Γ ⟹ f) ⇔ f[(bd_const c) /0] :=
begin
  unfold defines_constant at h_Γ, rw[completeness _ _] at h_Γ,
  rw[completeness _ _], intros M h_nonempty hM,
  have := h_Γ h_nonempty hM, simp only [fol.realize_sentence_biimp, fol.realize_bounded_formula, fol.realize_bounded_term, fol.realize_sentence_all, realize_subst_formula0, graph_relation_constant, fol.realize_bounded_formula_biimp] at *,
 split,
  {intro H, apply H, apply (this (realize_closed_term M (bd_const c))).mpr, refl},
  {intros H x H', convert H, exact (this x).mp H'}
end

lemma graph_relation_constant_elimination {L} {T : Theory L} {c : L.constants} {f : bounded_formula L 1} : T ⊢' ∀'(graph_relation_constant c ⟹ f) ⇔ f[(bd_const c) /0] :=
 by {apply defines_constant_elimination, exact graph_relation_constant_defines_constant}

end const

@[reducible, simp]def first_n_variables {L : Language} : ∀ n, dvector (bounded_term L n) n
| 0 := []
| 1 := [&0]
| (n+1) := ((first_n_variables n).map $ λ t, bounded_preterm.cast (by repeat{constructor} : n ≤ n +1) t).concat $ &(⟨n, by {repeat{constructor}}⟩: fin (n+1))

lemma first_n_variables_trunc {L : Language} : ∀ n m, (@first_n_variables L (n+m)).trunc n (by simp) = (@first_n_variables L n).map (λ t, t.cast (by simp)) := sorry

def graph_relation {n} {L : Language} (f : L.functions n) : bounded_formula L (n+1) :=
(bd_apps (bd_func f) (first_n_variables n)).cast1 ≃ bd_var (⟨n, by {repeat{constructor}}⟩)

-- lemma first_n_func_realize {n} {L : Language} {S : Structure L} (f : L.functions (n+1)) (xs : dvector S (n+1)) : realize_bounded_term xs (bd_apps (bd_func f) (first_n_variables (n+1))) dvector.nil = realize_bounded_term (xs.trunc n (by repeat{constructor})) (@bd_apps' L n 1 n ((bd_func f).cast_eq (by rw[add_comm] : n + 1 = 1 + n)) (first_n_variables n)) ([xs.last])

lemma function_semantics {n} {L : Language} {f : L.functions n} {S:Structure L} {xs : dvector S n} : realize_bounded_term xs (bd_apps (bd_func f) (first_n_variables n)) dvector.nil = S.fun_map f xs := sorry

lemma realize_first_n_variables {n : ℕ} {L : Language} {M : Structure L} {xs : dvector ↥M (n + 1)} : dvector.map (λ (t : bounded_term L n), realize_bounded_term (dvector.trunc n (by simp) xs) t dvector.nil) (first_n_variables n) = dvector.trunc n (by simp) xs :=
begin
  induction n, refl, rcases xs with ⟨x,xs⟩,
  have := @n_ih xs_xs, simp, conv {to_rhs, rw[<-this]}, sorry 
end

lemma graph_relation_soundness {n} {L : Language} {f : L.functions n} {M : Structure L} {xs : dvector M (n+1)}: (M.fun_map f (xs.trunc n (by repeat{constructor})) = xs.last) ↔ (realize_bounded_formula xs (graph_relation f) dvector.nil) :=
begin
unfold graph_relation; simp only [fol.bd_apps, fol.realize_bounded_formula, fol.first_n_variables, fol.realize_bounded_term, dvector.nth, realize_bounded_term_bd_apps, bounded_preterm.cast1,realize_cast_bounded_term];
  unfold dvector.last; split; intros; rw[<-a]; rw[realize_first_n_variables]; refl
end

end fol

namespace fol
namespace Lhom

section conservativity

notation ϕ`[[`:95 T₁`]]`:90 := Lhom.Theory_induced ϕ T₁ 
-- notation ϕ`[[`:95 f`]]`:90 := Lhom.on_sentence ϕ f
notation ϕ`[[`:95 f`]]`:90 := Lhom.on_bounded_formula ϕ f

/-- Given an L₁-theory T₁, an L₂-theory T₂ such that h : ϕ[T₁] ⊆ ϕ[T₂], we say that that T₂ is conservative over T₁ at f if h is conservative at ϕ[f]. -/

@[reducible, simp]def conservative {L₁ L₂} (ϕ : L₁ →ᴸ L₂) (T₁ : Theory L₁) (T₂ : Theory L₂) (f : sentence L₁) (h : ϕ[[T₁]] ⊆ T₂) :=
  fol.conservative h $ ϕ[[f]]

private lemma conservative_sanity_check {L₁ L₂ : Language} (ϕ : L₁ →ᴸ L₂) (T₁ : Theory L₁) (T₂ : Theory L₂) (f : sentence L₁) (h : ϕ[[T₁]] ⊆ T₂) :
 conservative ϕ T₁ T₂ f h ↔ ((ϕ[[T₁]] ⊢' ϕ[[f]]) ↔ T₂ ⊢' ϕ[[f]]) := by refl -- phew

/- An L₂-structure M₂ is the expansion along ϕ is an L₁-structure M₁ if M₁ is equal to the ϕ-reduct of M₂. -/  
@[reducible, simp]def is_expansion {L₁ L₂} (ϕ : L₁ →ᴸ L₂) (M₂ : Structure L₂) (M₁ : Structure L₁) := M₁ = M₂[[ϕ]]

theorem by_conservativity {L₁ L₂} (ϕ : L₁ →ᴸ L₂) (h_ϕ : is_injective ϕ) (M₂ : Structure L₂) (M₁ : Structure L₁)
  (h_expansion : is_expansion ϕ M₂ M₁)
  {T₁ : Theory L₁} {T₂ : Theory L₂} (f : sentence L₁) {h_M₁ : M₁ ⊨ T₁} {h_M₂ : M₂ ⊨ T₂}
  {h : ϕ[[T₁]] ⊆ T₂} :
    M₂ ⊨ ϕ[[f]] → M₁ ⊨ f :=
λ H, by {unfold is_expansion at h_expansion, rw[h_expansion], exact reduct_ssatisfied h_ϕ H}

theorem by_conservativity' {L₁ L₂} (ϕ : L₁ →ᴸ L₂) (h_ϕ : is_injective ϕ) (M₂ : Structure L₂) (M₁ : Structure L₁)
  (h_expansion : is_expansion ϕ M₂ M₁) 
  (T₁ : Theory L₁) (T₂ : Theory L₂) (f : sentence L₁) (h_M₁ : M₁ ⊨ T₁) (h_M₂ : M₂ ⊨ T₂)
  (h : ϕ[[T₁]] ⊆ T₂) (f' : sentence L₂)
  (h_equiv : M₂ ⊨ ϕ[[f]] ↔ M₂ ⊨ f') :
    M₂ ⊨ f' → M₁ ⊨ f :=
λ H, by {unfold is_expansion at h_expansion, rw[h_expansion],
             apply reduct_ssatisfied h_ϕ, exact h_equiv.mpr H}

end conservativity

-- TODO use typeclasses to handle bookkeeping of hierarchy of expansions of a type?
section test
universe u

theorem by_conservativity_constant
{L₁ L₂ : Language.{u}} {c : L₂.constants} {Γ : bounded_formula L₁ 1}
{T₁ : Theory L₁} {T₂ : Theory L₂} {ϕ : L₁ →ᴸ L₂} {h_ϕ : is_injective ϕ}
{h_Γ : @defines_constant L₂ T₂ (ϕ[[Γ]]) c} {h_sub : ϕ[[T₁]] ⊆ T₂} {M₁ : Structure L₁} {H_M₁ : M₁ ⊨ T₁} {M₂ : Structure L₂} {H_M₂ : M₂ ⊨ T₂} {h_exp : is_expansion ϕ M₂ M₁} {h_nonempty_1 : nonempty M₁} {h_nonempty_2 : nonempty M₂} :
∀ f : bounded_formula L₁ 1, M₂ ⊨ (ϕ[[f]])[(bd_const c) /0] → M₁ ⊨ ∀'(Γ ⟹ f) :=
begin
  intro f, have := (completeness _ _).mp
          (@defines_constant_elimination L₂ T₂ c (ϕ[[f]]) (ϕ[[Γ]]) h_Γ) h_nonempty_2 H_M₂,
  rw[realize_sentence_biimp] at this, rw[<-this], have : ∀'(ϕ[[Γ]] ⟹ ϕ[[f]]) = (ϕ[[∀'(Γ ⟹ f)]]),
  by refl, rw[this], apply by_conservativity ϕ h_ϕ M₂ M₁ h_exp ∀'(Γ ⟹ f), repeat{assumption}
end

-- TODO instantiate this for ZFC and ZFC'

end test

end Lhom
end fol
