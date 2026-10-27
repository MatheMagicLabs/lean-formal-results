/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.finite_fromRel_iff
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 140
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem finite_fromRel_iff : (fromRel sym).Finite ↔ Finite { p : α × α // r p.fst p.snd } := by
  constructor
  · intro h
    have h1 := cardinalMk_prod_le_two_mul_cardinalMk_fromRel sym
    rw [← Cardinal.lt_aleph0_iff_finite]
    have h2 : #(fromRel sym) < Cardinal.aleph0 := Cardinal.lt_aleph0_iff_set_finite.mpr h
    exact h1.trans_lt (Cardinal.mul_lt_aleph0 (by simpa using Cardinal.nat_lt_aleph0 2) h2)
  · intro h
    have h3 : (Sym2.mk.uncurry '' {p : α × α | r p.1 p.2}).Finite :=
      Set.Finite.image _ (Set.finite_coe_iff.mp h)
    refine h3.subset ?_
    rintro ⟨⟨a, b⟩⟩ hab
    exact ⟨(a, b), Sym2.fromRel_prop.mp hab, rfl⟩
