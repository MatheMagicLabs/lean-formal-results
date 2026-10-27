/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.closure_image_coe_ofPred_map_lt
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 346
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
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
    rcases eq_or_ne x 0 with rfl | h
    · show v.extension 0 < r
      rw [map_zero]
      exact zero_lt_iff.2 hr
    · obtain ⟨_, hy, a, ha, rfl⟩ := mem_closure_iff_nhds.1 hx _ (v.extension_locally_const h)
      have hy' : v.extension (a : Completion K) = v.extension x := hy
      have ha' : v a < r := ha
      show v.extension x < r
      rw [← hy', extension_apply_coe]
      exact ha'
  · intro x hx
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨a, ha, hva⟩ := v.exists_coe_mem_extension_eq hU
    refine ⟨a, ha, a, ?_, rfl⟩
    have hx' : v.extension x < r := hx
    show v a < r
    rw [← hva]
    exact hx'
