/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Measurable.sdiff_finset
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean, line 1084
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[fun_prop]
lemma Measurable.sdiff_finset (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a ↦ f a \ g a := by
  simp_rw [measurable_finset_iff_measurable_set, Finset.coe_sdiff]
  exact (measurable_finset_iff_measurable_set.1 hf).sdiff
    (measurable_finset_iff_measurable_set.1 hg)
