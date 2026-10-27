/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.continuous_extensionFun
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 240
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private theorem continuous_extensionFun : Continuous v.extensionFun := by
  show Continuous (Completion.isDenseInducing_coe.extend v.restrict)
  refine Completion.isDenseInducing_coe.continuous_extend ?_
  intro x₀
  rcases eq_or_ne x₀ 0 with rfl | hx₀
  · refine ⟨0, ?_⟩
    rw [← Completion.coe_zero, ← Completion.isDenseInducing_coe.nhds_eq_comap]
    exact (continuous_restrict v).tendsto' 0 0 (map_zero _)
  · obtain ⟨z₀, hz₀, h⟩ := exists_eventually_map_eq v hx₀
    refine ⟨v.restrict z₀, ?_⟩
    refine Tendsto.congr' ?_ tendsto_const_nhds
    refine h.mono fun x hx => ?_
    have h1 : ¬ v.restrict x < v.restrict z₀ := fun hl => (v.restrict_lt_iff.1 hl).ne hx
    have h2 : ¬ v.restrict z₀ < v.restrict x := fun hl => (v.restrict_lt_iff.1 hl).ne' hx
    exact le_antisymm (not_lt.1 h1) (not_lt.1 h2)
