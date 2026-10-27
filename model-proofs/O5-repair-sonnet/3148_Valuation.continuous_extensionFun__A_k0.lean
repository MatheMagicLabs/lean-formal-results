/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.continuous_extensionFun
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 240
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private theorem continuous_extensionFun : Continuous v.extensionFun := by
  refine Completion.isDenseInducing_coe.continuous_extend ?_
  intro x₀
  rcases eq_or_ne x₀ 0 with rfl | h
  · refine ⟨0, ?_⟩
    rw [← Completion.coe_zero, ← Completion.isDenseInducing_coe.nhds_eq_comap]
    exact (continuous_restrict v).tendsto' 0 0 (map_zero _)
  · obtain ⟨z₀, hz₀, hev⟩ := exists_eventually_map_eq v h
    refine ⟨v.restrict z₀, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [hev] with x hx
    refine le_antisymm (not_lt.1 fun hl => ?_) (not_lt.1 fun hl => ?_)
    · rw [v.restrict_lt_iff] at hl
      rw [hx] at hl
      exact lt_irrefl _ hl
    · rw [v.restrict_lt_iff] at hl
      rw [hx] at hl
      exact lt_irrefl _ hl
