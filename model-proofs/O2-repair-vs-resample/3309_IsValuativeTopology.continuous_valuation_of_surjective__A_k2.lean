/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsValuativeTopology.continuous_valuation_of_surjective
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 142
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem continuous_valuation_of_surjective (hsurj : Function.Surjective v) : Continuous v := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  by_cases hx : v x = 0
  · obtain rfl : x = 0 := (Valuation.zero_iff v).1 hx
    rw [ContinuousAt, hx, WithZeroTopology.tendsto_zero]
    intro γ hγ
    obtain ⟨y, rfl⟩ := hsurj γ
    exact eventually_lt_nhds_zero v hγ
  · exact continuousAt_valuation_of_ne_zero v hx
