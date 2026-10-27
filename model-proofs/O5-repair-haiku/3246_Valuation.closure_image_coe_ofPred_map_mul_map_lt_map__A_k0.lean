/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.closure_image_coe_ofPred_map_mul_map_lt_map
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 359
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-haiku, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-haiku-4-5
Setup:       Haiku 4.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem closure_image_coe_ofPred_map_mul_map_lt_map {r s : K} (hr : r ≠ 0) (hs : s ≠ 0) :
    closure ((↑) '' {x : K | v x * v r < v s}) =
    {x : Completion K | v.extension x * v r < v s} := by
  ext x
  simp only [mem_ofPred_eq, mem_closure_iff_nhds]
  refine ⟨fun hx ↦ ?_, fun hx t ht ↦ ?_⟩
  · rcases eq_or_ne x 0 with rfl | h
    · simp [zero_mul, zero_lt_iff, hs]
    · obtain ⟨_, hy : v.extension _ = v.extension x, y, hy' : v y * v r < v s, rfl⟩ :=
        hx _ (v.extension_locally_const h)
      rwa [← hy, extension_apply_coe]
  · obtain ⟨y, hy, hy'⟩ := v.exists_coe_mem_extension_eq ht
    exact ⟨y, hy, y, by simpa [← hy'] using hx, rfl⟩
