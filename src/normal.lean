import .fol tactic.tidy .peano

open fol

local notation h :: t  := dvector.cons h t
local notation `[]` := dvector.nil
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

/- Some normal forms for formulas -/

namespace nnf
section

open peano



end
end nnf
