/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.closure_image_coe_ofPred_map_lt
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 346
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem closure_image_coe_ofPred_map_lt {r : Γ₀} (hr : r ≠ 0) :
    closure ((↑) '' {x : K | v x < r}) = {x : Completion K | v.extension x < r} := by
  apply subset_antisymm
  · intro x hx
    by_contra h
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact h (by simp [zero_lt_iff, hr])
    obtain ⟨_, hyU, z, hz, rfl⟩ := mem_closure_iff_nhds.1 hx _ (v.extension_locally_const hx0)
    simp only [mem_setOf_eq, extension_apply_coe] at hyU hz
    apply h
    show v.extension x < r
    rw [← hyU]
    exact hz
  · intro x hx
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨s, hs, hv⟩ := v.exists_coe_mem_extension_eq hU
    refine ⟨s, hs, s, ?_, rfl⟩
    show v s < r
    rw [← hv]
    exact hx
