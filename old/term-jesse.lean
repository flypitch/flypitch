/-- Authors: Andrew Tindall, Jesse Han --/

structure Language :=
    language :: (consts : Type) (relations : Π n : nat, Type) (functions : Π  n : nat, Type)

variable L : Language

inductive term : ℕ → Type
  | nil {} : term 0
  | const : L.consts → term 1
  | var : nat → term 1
  | apply : ∀ (n : nat), ∀ (f : L.functions n), term n → term 1
  | conj : ∀ (n : nat), term 1 → term n → term (n + 1)

inductive formula : Type
  | equals : term L 1 → term L 1 → formula
  | apply : Π n : nat, L.relations n → term L n → formula
  | and : formula → formula → formula
  | or : formula → formula → formula
  | not : formula → formula
  | ex : formula → formula
  | all : formula → formula

def substitution_map_on_term (v : ℕ) (t : term L 1) : Π n : ℕ, term L n → term L n
  | 0 t := term.nil
  | k (term.var _ v) := t
  | 1 (term.apply n f s) := (term.apply n f) (substitution_map_on_term n s)
  | 1 (term.const c) := term.const c
  | (nat.succ k) (term.conj n a s) := (term.conj n (substitution_map_on_term 1 a) (substitution_map_on_term k s))

def substitution_map_on_formula (v : ℕ) (t : term L 1) : formula L → formula L
  | (formula.equals t1 t2) := (formula.equals (substitution_map_on_term L v t 1 t1)  (substitution_map_on_term L v t 1 t2))
  | (formula.apply n R s) := formula.apply n R (substitution_map_on_term L v t n s)
  | (formula.and A B) := formula.and (substitution_map_on_formula A) (substitution_map_on_formula B)
  | (formula.or A B) := formula.or (substitution_map_on_formula A) (substitution_map_on_formula B)
  | (formula.ex A) := formula.ex (substitution_map_on_formula A)
  | (formula.all A) := formula.all (substitution_map_on_formula A)
  | (formula.not A) := formula.not (substitution_map_on_formula A)

