/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.closure_image_coe_ofPred_restrict_lt
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 420
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem closure_image_coe_ofPred_restrict_lt (γ : v.ValueGroup₀ˣ) :
    closure ((↑) '' {x : K | v.restrict x < γ.1}) =
      {x : Completion K | v.extension x < embedding γ.1} := by
  have hr : embedding γ.1 ≠ 0 := by
    simpa using γ.ne_zero
  have h : {x : K | v.restrict x < γ.1} = {x : K | v x < embedding γ.1} := by
    ext x
    simp [restrict_lt_iff_lt_embedding]
  rw [h]
  exact v.closure_image_coe_ofPred_map_lt hr
