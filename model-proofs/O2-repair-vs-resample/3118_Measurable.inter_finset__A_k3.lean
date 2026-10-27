/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Measurable.inter_finset
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean, line 1070
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[fun_prop]
lemma Measurable.inter_finset (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a ↦ f a ∩ g a := by
  refine measurable_finset_iff.2 fun a ↦ ?_
  simp only [Finset.mem_inter]
  exact (measurable_finset_iff.1 hf a).and (measurable_finset_iff.1 hg a)
