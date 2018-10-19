import .language_term_n2

open fol

section zfc

inductive ZFC_rel
| ϵ

def L_ZFC : Language := 
begin
split,
{ intro arityf,
exact empty},
{intro arityr,
exact if arityr = 2 then ZFC_rel else empty},
end

#print L_ZFC -- good


inductive ZFC'_f0 : Type
| emptyset

inductive ZFC'_f1 : Type
| union
| pow

inductive ZFC'_f2 : Type
| pair

def L_ZFC' : Language :=
begin
split,
{intro arityf,
exact if arityf = 0
      then ZFC'_f0
      else (if arityf = 1
           then ZFC'_f1
           else (if arityf = 2
                then ZFC'_f2
                else empty))   },
{
{intro arityr,
exact if arityr = 2 then ZFC_rel else empty},
}
end

-- is there a way to do this with the equation compiler instead?

#print L_ZFC'

/- state the ZFC axioms using L_ZFC' and prove that they are sentences -/

def axiom_of_emptyset : @sentence L_ZFC' := -- for all x, x is not in the constant emptyset.
begin
split,
{sorry},
{
simp[formula],
{exact sorry}
}
end

def axiom_of_extensionality : @sentence L_ZFC' := -- for all x for all y for all z, z in x iff z in y implies x = y
begin
split,
{sorry},
{
simp[formula],
{exact sorry}
}
end

-- etc

inductive ZFC' : (@sentence L_ZFC') → Prop -- should this be Type-valued instead?
:= sorry

end zfc

