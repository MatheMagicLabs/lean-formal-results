/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ClassGroup.map_id
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/ClassGroup/ExtendedHom.lean, line 68
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp]
theorem map_id (x : ClassGroup A) : map (RingHom.id A) Function.injective_id x = x := by
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
  rw [map_quotientMk]
  congr 1
  ext1
  simp only [Units.coe_map, MonoidHom.coe_coe]
  apply FractionalIdeal.coeToSubmodule_injective
  first
  | simp [FractionalIdeal.coe_extended_eq_span, IsLocalization.map_id, Set.image]
  | simp [FractionalIdeal.extendedHom', FractionalIdeal.coe_extended_eq_span,
      IsLocalization.map_id, Set.image]
  all_goals first
    | exact Submodule.span_eq _
    | exact Submodule.span_eq ((α : FractionalIdeal A⁰ (FractionRing A)) :
        Submodule A (FractionRing A))
