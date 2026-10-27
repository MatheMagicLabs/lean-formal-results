/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.continuous_extensionFun
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 240
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private theorem continuous_extensionFun : Continuous v.extensionFun := by
  unfold extensionFun
  refine Completion.isDenseInducing_coe.continuous_extend fun b => ?_
  by_cases hb : b = 0
  · subst hb
    refine ⟨0, ?_⟩
    have h := Completion.isDenseInducing_coe.isInducing.nhds_eq_comap (0 : K)
    rw [Completion.coe_zero] at h
    rw [← h]
    have := (continuous_restrict v).tendsto 0
    simpa using this
  · obtain ⟨z₀, hz, hev⟩ := exists_eventually_map_eq v hb
    refine ⟨v.restrict z₀, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [hev] with x hx
    refine le_antisymm (not_lt.1 fun h => ?_) (not_lt.1 fun h => ?_)
    · have := v.restrict_lt_iff.1 h
      rw [hx] at this
      exact lt_irrefl _ this
    · have := v.restrict_lt_iff.1 h
      rw [hx] at this
      exact lt_irrefl _ this
