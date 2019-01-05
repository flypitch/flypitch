import .fol

open fol

/- ZFC in expanded signature -/

namespace zfc'

inductive ZFC'_functions : ℕ → Type
| emptyset : ZFC'_functions 0
| union : ZFC'_functions 1
| pow : ZFC'_functions 1
| pair : ZFC'_functions 2


inductive ZFC'_relations : ℕ → Type
| ϵ : ZFC'_relations 2
| subset : ZFC'_relations 2

def L_ZFC' : Language :=
⟨ZFC'_functions, ZFC'_relations⟩

end zfc'
