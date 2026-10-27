/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.exists_coe_mem_extension_eq
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 311
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma exists_coe_mem_extension_eq {x : Completion K} {U : Set (Completion K)} (hU : U ∈ 𝓝 x) :
    ∃ r : K, (r : Completion K) ∈ U ∧ v.extension x = v r := by
  rcases eq_or_ne x 0 with rfl | hx
  · refine ⟨0, ?_, ?_⟩
    · rw [Completion.coe_zero]; exact mem_of_mem_nhds hU
    · simp
  · obtain ⟨_, ⟨hrU, hr⟩, r, rfl⟩ := mem_closure_iff_nhds.1 (Completion.denseRange_coe x) _
      (inter_mem hU (v.extension_locally_const hx))
    exact ⟨r, hrU, (show v.extension (r : Completion K) = v.extension x from hr).symm.trans
      (v.extension_apply_coe r)⟩
