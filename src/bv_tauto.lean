import .to_mathlib

local infix ` ⟹ `:65 := lattice.imp

namespace lattice

lemma context_or_elim' {β} [complete_boolean_algebra β] {Γ a b c : β} (H : Γ ≤ a ⊔ b) (H_left : ∀ {Γ'} (H_le : Γ' ≤ Γ) (H_le' : Γ' ≤ a), Γ' ≤ c) (H_right : ∀ {Γ'} (H_le : Γ' ≤ Γ) (H_le' : Γ' ≤ b), Γ' ≤ c) : Γ ≤ c :=
begin
  bv_or_elim_at H,
    { specialize @H_left Γ_1 (by simp[Γ_1]) ‹_›, from ‹_› },
    { specialize @H_right Γ_1 (by simp[Γ_1]) ‹_›, from ‹_› }
end

end lattice


namespace tactic
namespace interactive
section bv_tauto
open lean.parser lean interactive.types interactive
local postfix `?`:9001 := optional

-- takes `e`, a proof that Γ' ≤ Γ, and specializes hypotheses of the form `Γ  ≤ b` to `Γ' ≤ b`
meta def context_switch_core (e : expr) : tactic unit :=
do `(%%Γ' ≤ %%Γ) <- infer_type e,
   ctx <- local_context >>=
            (λ l, l.mfilter (λ H,
               ((do Γ'' <- (infer_type H) >>= lhs_of_le,
                 succeeds (is_def_eq Γ'' Γ))) <|> return ff)),
   ctx.mmap' ((λ H, do let n := get_name H,
                       prf <- to_expr ``(le_trans %%e %%H),
                       note n none prf,
                       tactic.clear H) : expr → tactic unit)

meta def context_switch (p : parse texpr): tactic unit :=
do e <- to_expr ``(%%p),
  context_switch_core e

-- faster version of bv_or_elim
-- TODO(jesse): `cases`-like handling of new names for the split hypotheses
-- TODO(jesse): add similar versions with bv_impl_intro and bv_exists_elim
meta def bv_or_elim_core (p : expr) : tactic unit :=
do  n <- get_unused_name "Γ",
    n_H <- get_unused_name "H_le",
    `[apply lattice.context_or_elim' %%p];
    propagate_tags ((intro_lst [n,n_H]) >> skip);
    tactic.clear p;
    resolve_name n_H >>= context_switch; intro none

meta def bv_or_elim (n : parse ident) : tactic unit :=
resolve_name n >>= to_expr >>= bv_or_elim_core

meta def auto_or_elim_aux : list expr → tactic unit
| [] := tactic.fail "auto_or_elim failed"
| (e::es) := (do `(%%Γ ≤ %%x ⊔ %%y) <- infer_type e,
                let n := get_name e,
                Γ₁ <- get_current_context >>= whnf,
                Γ₂ <- whnf Γ,
                guard (Γ₁ =ₐ Γ₂),
                bv_or_elim_core e,
                try assumption)
                <|> auto_or_elim_aux es

meta def auto_or_elim_step : tactic unit := local_context >>= auto_or_elim_aux

meta def goal_is_bv_false : tactic unit :=
do rhs <- target >>= rhs_of_le,
   match rhs with
   | `(⊥) := skip
   | _ := fail "not ⊥"
   end

meta def bv_tauto_step : tactic unit :=
do (goal_is_bv_false >> skip) <|> `[refine _root_.lattice.bv_by_contra _] >> bv_imp_intro none,
   `[try {unfold _root_.lattice.imp at *}],
   `[try {simp only with bv_push_neg at *}],
   try bv_split,
   try bv_contradiction

meta def bv_tauto (n : option ℕ := none) : tactic unit :=
match n with
| none := bv_tauto_step *> (done <|> (auto_or_elim_step; bv_tauto))
| (some k) := iterate_at_most k bv_tauto_step
end

end bv_tauto
end interactive
end tactic

example {𝔹} [lattice.nontrivial_complete_boolean_algebra 𝔹] {a b c : 𝔹} : ( a ⟹ b ) ⊓ ( b ⟹ c ) ≤ a ⟹ c :=
begin
  tidy_context, bv_tauto
end
