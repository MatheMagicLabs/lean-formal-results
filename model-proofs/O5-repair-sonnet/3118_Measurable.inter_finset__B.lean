/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Measurable.inter_finset
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean, line 1070
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[fun_prop]
lemma Measurable.inter_finset (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a ↦ f a ∩ g a := by
  rw [measurable_finset_iff]
  intro a
  simp only [Finset.mem_inter]
  exact (measurable_finset_iff.1 hf a).and (measurable_finset_iff.1 hg a)
