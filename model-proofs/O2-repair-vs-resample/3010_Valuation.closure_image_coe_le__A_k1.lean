/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.closure_image_coe_le
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 332
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma closure_image_coe_le : closure ((Prod.map (↑) (↑)) '' {(x, y) : K × K | v x ≤ v y}) =
    {(x, y) | v.extension x ≤ v.extension y} := by
  apply Subset.antisymm
  · refine closure_minimal ?_ ?_
    · rintro _ ⟨⟨a, b⟩, hab, rfl⟩
      show v.extension (a : Completion K) ≤ v.extension (b : Completion K)
      rw [extension_apply_coe, extension_apply_coe]
      exact hab
    · convert isClosed_le (v.continuous_extensionFun.comp continuous_fst)
        (v.continuous_extensionFun.comp continuous_snd) using 1
      ext ⟨x, y⟩
      exact v.extension_le_iff_extensionFun_le
  · rintro ⟨x, y⟩ h
    change v.extension x ≤ v.extension y at h
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨r, s, hrs, hr, hs⟩ := v.exists_coe_mem_extension_eq₂ hU
    refine ⟨_, hrs, ⟨(r, s), ?_, rfl⟩⟩
    show v r ≤ v s
    rw [← hr, ← hs]
    exact h
