/-
Proof system for the locally-nameless representation of first-order logic
following the notes at /flypitch-notes

Thanks to Andrew who wrote the prototypical examples in language_term_n*
---Jesse 2018-10-16T00:00:50
-/

import .language_term_ln2

axiom list_nil_lemma : @list.nil ℕ ∪ list.nil = list.nil

section
parameter L : Language

def arity (α β : Type) : nat → Type -- thanks Seul!!
| 0 := β 
| (n+1) := α → arity n

-- inductive closed_preterm :Π n : ℕ,  preterm L n → Prop
-- | bvar : Π k : ℕ, closed_preterm 0 (preterm.bvar L k)
-- | func : Π n : ℕ, Π f : L.functions n, closed_preterm n (preterm.func f)
-- | apply : Π n : ℕ, Π t1 : (preterm L (n+1)), Π t2 : (preterm L 0), Π h1 : (closed_preterm (n+1) t1), Π h2 : (closed_preterm 0 t2), closed_preterm n (preterm.apply t1 t2)


-- inductive presentence : Π(n : ℕ), preformula L n → Prop
-- | true : presentence 0 (preformula.true L)
-- | false : presentence 0 (preformula.false L)
-- | equal : Π t1 t2 : term L, Π h1 : closed_preterm 0 t1, Π h2 : closed_preterm 0 t2, presentence 0 (preformula.equal t1 t2)
-- | rel : Π {n : ℕ}, Π R : L.relations n, presentence n (preformula.rel R)
-- | apprel : Π {n : ℕ}, Π ψ : preformula L (n+1), Π t : term L, Π h1 : presentence (n+1) ψ, Π h2 : closed_preterm 0 t, presentence n (preformula.apprel ψ t)
-- | imp : Π ϕ : preformula L 0, Π ψ : preformula L 0, Π h1 : presentence 0 ϕ, Π h2 : presentence 0 ψ, presentence 0 (preformula.imp ϕ ψ)
-- | all : Π ψ : preformula L 0, Π h : presentence 0 ψ, presentence 0 (preformula.all ψ) -- this is wrong
--
-- def sentence : formula L → Prop := presentence 0

/-- A sentence is a well-formed L-formula with no free variables --/
def is_sentence : formula L → Prop := λ ψ, (free_vars_formula L ψ = []) ∧ well_formed_formula L ψ
def sentences := {ψ : formula L // is_sentence ψ}

lemma true_is_sentence : is_sentence (preformula.true L) :=
begin
split,
{split,},
{trivial}
end

lemma false_is_sentence : is_sentence (preformula.false L) :=
begin
split,
{split},
{split}
end



lemma imp_is_sentence (ϕ : sentences) (ψ : sentences) : is_sentence (preformula.imp (ϕ.val) (ψ.val)) :=
begin
split,
  {cases ϕ,
  cases ψ,
  simp[free_vars_formula],
  cases ϕ_property,
  cases ψ_property,
  simp[free_vars_preformula], 
  have h :list.nil ∪ list.nil = list.nil,
    {exact list_nil_lemma},
  have h1 : free_vars_preformula L 0 ϕ_val = free_vars_formula L ϕ_val,
    {refl},
  have h2 :  free_vars_preformula L 0 ψ_val = free_vars_formula L ψ_val,
    {refl},
  simp [h1, h2],
  rw [ϕ_property_left, ψ_property_left],
  assumption  },
{split,
  {exact and.right (ϕ.property)},
  {exact and.right (ψ.property)}, }
end

#reduce true_is_sentence

-- For now, I am deciding against a proof system with nonempty contexts.

-- reflecting Prop-tautologies into sentences L

inductive propositional_combination : ((list (sentences)) → sentences) → Prop
| true : propositional_combination (λ xs, ⟨preformula.true L, true_is_sentence⟩)
| false : propositional_combination (λ xs, ⟨preformula.false L, false_is_sentence⟩)
| imp : Π f g : ((list (sentences)) → sentences), Π hf : propositional_combination f, Π hg : propositional_combination g, propositional_combination (λ xs, ⟨preformula.imp (f xs).val (g xs).val, imp_is_sentence⟩)

-- TODO: get all projections, get all propositional combinations thereof.

end
