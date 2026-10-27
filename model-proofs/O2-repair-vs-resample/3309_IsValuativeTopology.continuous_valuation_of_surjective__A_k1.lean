/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsValuativeTopology.continuous_valuation_of_surjective
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 142
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem continuous_valuation_of_surjective (hsurj : Function.Surjective v) : Continuous v := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases h : v x = 0
  · have hx : x = 0 := v.zero_iff.mp h
    subst hx
    rw [ContinuousAt, v.map_zero, WithZeroTopology.tendsto_zero]
    intro γ hγ
    obtain ⟨y, rfl⟩ := hsurj γ
    exact IsValuativeTopology.eventually_lt_nhds_zero v hγ
  · exact IsValuativeTopology.continuousAt_valuation_of_ne_zero v h
