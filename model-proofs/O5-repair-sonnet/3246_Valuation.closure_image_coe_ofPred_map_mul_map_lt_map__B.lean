/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.closure_image_coe_ofPred_map_mul_map_lt_map
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 359
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem closure_image_coe_ofPred_map_mul_map_lt_map {r s : K} (hr : r ≠ 0) (hs : s ≠ 0) :
    closure ((↑) '' {x : K | v x * v r < v s}) =
    {x : Completion K | v.extension x * v r < v s} := by
  ext x
  have hs' : v s ≠ 0 := v.ne_zero_iff.2 hs
  simp only [mem_closure_iff_nhds, mem_setOf_eq]
  constructor
  · intro hx
    rcases eq_or_ne x 0 with rfl | h
    · simp [zero_lt_iff, hs']
    · obtain ⟨_, hy : v.extension _ = v.extension x, y, hy', rfl⟩ :=
        hx _ (v.extension_locally_const h)
      rw [← hy, extension_apply_coe]
      exact hy'
  · intro hx t ht
    obtain ⟨y, hy, hy'⟩ := v.exists_coe_mem_extension_eq ht
    refine ⟨y, hy, y, ?_, rfl⟩
    show v y * v r < v s
    rw [← hy']
    exact hx
