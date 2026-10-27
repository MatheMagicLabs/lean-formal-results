/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.closure_image_coe_ofPred_map_lt
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 346
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem closure_image_coe_ofPred_map_lt {r : Γ₀} (hr : r ≠ 0) :
    closure ((↑) '' {x : K | v x < r}) = {x : Completion K | v.extension x < r} := by
  apply subset_antisymm
  · refine closure_minimal ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      show v.extension (y : Completion K) < r
      rw [extension_apply_coe]
      exact hy
    · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro x hx
      have hx' : r ≤ v.extension x := not_lt.1 hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        have h0 : v.extension (0 : Completion K) = 0 := map_zero _
        rw [h0] at hx'
        exact hr (le_antisymm hx' zero_le')
      filter_upwards [v.extension_locally_const hx0] with y hy
      have hy' : v.extension y = v.extension x := hy
      show ¬ v.extension y < r
      rw [hy']
      exact not_lt.2 hx'
  · intro x hx
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨s, hs, hvs⟩ := v.exists_coe_mem_extension_eq hU
    have hx' : v.extension x < r := hx
    have hsr : v s < r := by rw [← hvs]; exact hx'
    exact ⟨(s : Completion K), hs, s, hsr, rfl⟩
