/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Convex.openSegment_image_interior_closure_preimage_subset
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Convex/Topology.lean, line 154
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem Convex.openSegment_image_interior_closure_preimage_subset {F : Type*}
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousConstSMul 𝕜 F] {A : F →ᵃ[𝕜] E} {s} (hs : Convex 𝕜 s)
    {x y} (hx : x ∈ interior (A ⁻¹' s)) (hy : y ∈ closure (A ⁻¹' s)) :
    openSegment 𝕜 (A x) (A y) ⊆ A '' interior (A ⁻¹' s) := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨a • x + b • y, ?_, ?_⟩
  · exact (hs.affine_preimage A).combo_interior_closure_mem_interior hx hy ha hb.le hab
  · exact Convex.combo_affine_apply hab
