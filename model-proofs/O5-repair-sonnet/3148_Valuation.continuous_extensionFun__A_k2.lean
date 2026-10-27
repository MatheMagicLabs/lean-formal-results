/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.continuous_extensionFun
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 240
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private theorem continuous_extensionFun : Continuous v.extensionFun := by
  show Continuous (Completion.isDenseInducing_coe.extend v.restrict)
  refine Completion.isDenseInducing_coe.continuous_extend fun x₀ ↦ ?_
  rcases eq_or_ne x₀ 0 with rfl | h
  · refine ⟨0, ?_⟩
    have hc : Filter.comap ((↑) : K → Completion K) (𝓝 (0 : Completion K)) = 𝓝 (0 : K) := by
      rw [← Completion.coe_zero, ← Completion.isDenseInducing_coe.isInducing.nhds_eq_comap]
    rw [hc]
    exact (continuous_restrict v).tendsto' 0 0 (map_zero _)
  · obtain ⟨z₀, hz₀, hev⟩ := exists_eventually_map_eq v h
    refine ⟨v.restrict z₀, ?_⟩
    refine Filter.Tendsto.congr' (hev.mono fun x hx ↦ ?_) tendsto_const_nhds
    symm
    apply le_antisymm
    · refine le_of_not_gt fun hlt ↦ ?_
      have := v.restrict_lt_iff.1 hlt
      rw [hx] at this
      exact lt_irrefl _ this
    · refine le_of_not_gt fun hlt ↦ ?_
      have := v.restrict_lt_iff.1 hlt
      rw [hx] at this
      exact lt_irrefl _ this
