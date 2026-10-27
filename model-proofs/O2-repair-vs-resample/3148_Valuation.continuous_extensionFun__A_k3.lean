/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.continuous_extensionFun
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 240
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private theorem continuous_extensionFun : Continuous v.extensionFun := by
  refine Completion.isDenseInducing_coe.continuous_extend fun x₀ ↦ ?_
  rcases eq_or_ne x₀ 0 with rfl | h
  · refine ⟨0, ?_⟩
    have := Completion.isDenseInducing_coe.isInducing.nhds_eq_comap (0 : K)
    rw [Completion.coe_zero] at this
    rw [← this]
    exact (continuous_restrict v).tendsto' 0 0 (map_zero _)
  · obtain ⟨z₀, hz₀, hev⟩ := v.exists_eventually_map_eq h
    refine ⟨v.restrict z₀, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [hev] with x hx
    exact (le_antisymm (not_lt.1 fun h' ↦ (v.restrict_lt_iff.1 h').ne' hx)
      (not_lt.1 fun h' ↦ (v.restrict_lt_iff.1 h').ne hx)).symm
