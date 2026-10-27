/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ClassGroup.map_id
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/ClassGroup/ExtendedHom.lean, line 68
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
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
  rw [Units.coe_map]
  apply FractionalIdeal.coeToSubmodule_injective
  change Submodule.span A (_ '' _) = _
  refine le_antisymm (Submodule.span_le.2 ?_)
    (fun z hz => Submodule.subset_span ⟨z, hz, IsLocalization.map_id z _⟩)
  rintro _ ⟨z, hz, rfl⟩
  simpa [IsLocalization.map_id] using hz
