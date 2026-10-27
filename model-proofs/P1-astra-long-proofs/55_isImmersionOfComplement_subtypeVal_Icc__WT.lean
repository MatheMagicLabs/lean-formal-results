/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     isImmersionOfComplement_subtypeVal_Icc
Source:      Mathlib @ d0a050ad6, Mathlib/Geometry/Manifold/Instances/Icc.lean, line 72
             (added after the model's training data; human proof 31 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 3 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma isImmersionOfComplement_subtypeVal_Icc :
    IsImmersionOfComplement Unit (𝓡∂ 1) 𝓘(ℝ) n (fun (z : Icc x y) ↦ (z : ℝ)) := by
  let e : (EuclideanSpace ℝ (Fin 1) × Unit) ≃L[ℝ] ℝ := (ContinuousLinearEquiv.prodUnique ℝ _ Unit).trans ((EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℝ)))
  intro z
  by_cases hz : z.val < y
  · {
  refine IsImmersionAtOfComplement.mk_of_charts e (IccLeftChart x y) (Homeomorph.subRight x).toOpenPartialHomeomorph hz (by trivial) ?_ ?_ (by intro a ha; trivial) ?_
  · {
  apply subset_maximalAtlas
  change IccLeftChart x y ∈ {IccLeftChart x y, IccRightChart x y}
  simp }
  · {
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (show ContDiff ℝ n (fun t : ℝ ↦ t - x) from contDiff_id.sub contDiff_const).contDiffOn.contMDiffOn
  · exact (show ContDiff ℝ n (fun t : ℝ ↦ t + x) from contDiff_id.add contDiff_const).contDiffOn.contMDiffOn }
  · {
  rw [OpenPartialHomeomorph.extend_target_eq_image_source]
  rintro _ ⟨a, ha, rfl⟩
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_left_inv _ ha]
  rfl } }
  · {
  have hz' : x < z.val := lt_of_lt_of_le h.out (le_of_not_gt hz)
  refine IsImmersionAtOfComplement.mk_of_charts e (IccRightChart x y) (Homeomorph.subLeft y).toOpenPartialHomeomorph hz' (by trivial) ?_ ?_ (by intro a ha; trivial) ?_
  · {
  apply subset_maximalAtlas
  change IccRightChart x y ∈ {IccLeftChart x y, IccRightChart x y}
  simp }
  · {
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (show ContDiff ℝ n (fun t : ℝ ↦ y - t) from contDiff_const.sub contDiff_id).contDiffOn.contMDiffOn
  · exact (show ContDiff ℝ n (fun t : ℝ ↦ y - t) from contDiff_const.sub contDiff_id).contDiffOn.contMDiffOn }
  · {
  rw [OpenPartialHomeomorph.extend_target_eq_image_source]
  rintro _ ⟨a, ha, rfl⟩
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_left_inv _ ha]
  rfl } }
