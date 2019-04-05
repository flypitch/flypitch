import .zfc'

open fol bSet pSet lattice

#print Language

#print preterm

#print preformula

#print term

#print formula

#print sentence

#print prf

#print provable

#print pSet

#print bSet

#print L_ZFC'

#print ZFC'

#print CH_f

def CH_sentence := CH_f

theorem fundamental_theorem_of_forcing {β} [nontrivial_complete_boolean_algebra β] :
  ⊤ ⊩[V β] ZFC' :=
begin
  change ⊤ ≤ _, bv_intro f, bv_intro H,
  repeat{auto_cases}; try{subst H}; try {cases H},
  from bSet_models_Zorn _,
  from bSet_models_regularity _,
  from bSet_models_infinity _,
  from bSet_models_powerset _,
  from bSet_models_union _,
  from bSet_models_extensionality _,
  from bSet_models_pairing _,
  from bSet_models_emptyset _,
  from bSet_models_collection _ ‹_›
end

theorem CH_unprovable_from_ZFC : ¬ (ZFC' ⊢' CH_sentence) :=
begin
  intro H,
  suffices forces_false : ⊤ ⊩[V 𝔹] bd_falsum,
    from absurd (nontrivial.bot_lt_top) (not_lt_of_le forces_false),
  refine forced_absurd _ _, exact ZFC', exact CH_f, swap, apply neg_CH_f,
  let prf_of_CH_f := sprovable_of_provable (classical.choice H),
  have CH_f_true := boolean_soundness prf_of_CH_f (V_𝔹_nonempty),
  convert CH_f_true, rw[inf_axioms_top_of_models (bSet_models_ZFC' _)]
end
