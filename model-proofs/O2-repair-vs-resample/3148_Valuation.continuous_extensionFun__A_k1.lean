/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.continuous_extensionFun
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 240
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private theorem continuous_extensionFun : Continuous v.extensionFun := by
  refine Completion.isDenseInducing_coe.continuous_extend fun x₀ ↦ ?_
  rcases eq_or_ne x₀ 0 with rfl | hx₀
  · refine ⟨0, ?_⟩
    rw [← Completion.coe_zero, ← Completion.isDenseInducing_coe.nhds_eq_comap]
    simpa using (continuous_restrict v).tendsto (0 : K)
  · obtain ⟨z₀, -, hz⟩ := v.exists_eventually_map_eq hx₀
    refine ⟨v.restrict z₀, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [hz] with x h
    exact (le_antisymm (not_lt.1 fun h' => (v.restrict_lt_iff.1 h').ne' h)
      (not_lt.1 fun h' => (v.restrict_lt_iff.1 h').ne h)).symm
