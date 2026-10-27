/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.closure_image_coe_ofPred_map_mul_map_lt_map
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 359
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem closure_image_coe_ofPred_map_mul_map_lt_map {r s : K} (hr : r ≠ 0) (hs : s ≠ 0) :
    closure ((↑) '' {x : K | v x * v r < v s}) =
    {x : Completion K | v.extension x * v r < v s} := by
  have hr' : v r ≠ 0 := v.ne_zero_iff.2 hr
  have hs' : v s ≠ 0 := v.ne_zero_iff.2 hs
  have key : ∀ a : Γ₀, a * v r < v s ↔ a < v s / v r := fun a => by
    rw [lt_div_iff₀ (zero_lt_iff.2 hr')]
  have h := closure_image_coe_ofPred_map_lt v (r := v s / v r) (div_ne_zero hs' hr')
  have e1 : {x : K | v x * v r < v s} = {x : K | v x < v s / v r} := by
    ext x
    exact key _
  rw [e1, h]
  ext x
  exact (key _).symm
