/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.closure_image_coe_ofPred_map_mul_map_lt_map
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 359
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem closure_image_coe_ofPred_map_mul_map_lt_map {r s : K} (hr : r ≠ 0) (hs : s ≠ 0) :
    closure ((↑) '' {x : K | v x * v r < v s}) =
    {x : Completion K | v.extension x * v r < v s} := by
  have hr' : v r ≠ 0 := by simpa using hr
  have hpos : (0 : Γ₀) < v r := zero_lt_iff.2 hr'
  have key : ∀ a : Γ₀, a * v r < v s ↔ a < v s / v r := by
    intro a
    first
    | exact (lt_div_iff₀ hpos).symm
    | exact (lt_div_iff₀' hpos).symm
    | constructor
      · intro h
        by_contra h'
        push_neg at h'
        have := mul_le_mul_right' h' (v r)
        rw [div_mul_cancel₀ _ hr'] at this
        exact absurd h (not_lt.2 this)
      · intro h
        have := mul_lt_mul_of_pos_right h hpos
        rwa [div_mul_cancel₀ _ hr'] at this
  have := v.closure_image_coe_ofPred_map_lt (r := v s / v r) (by simp [hr, hs])
  simp_rw [key]
  exact this
