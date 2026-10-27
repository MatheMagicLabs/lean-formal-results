/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ContinuousLinearMap.exists_eq_smulRightLₗ
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Operator/Bilinear.lean, line 494
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private lemma exists_eq_smulRightLₗ :
    ∃ g : StrongDual 𝕜 E' →L[𝕜] Fₗ' →L[𝕜] E' →L[𝕜] Fₗ',
      ∀ a b, smulRightLₗ 𝕜 E' Fₗ' a b = g a b := by
  let : SeminormedAddCommGroup E' := IsNormableSpace.toSeminormedAddCommGroup 𝕜 E'
  let : NormedSpace 𝕜 E' := IsNormableSpace.toNormedSpace 𝕜 E'
  let : SeminormedAddCommGroup Fₗ' := IsNormableSpace.toSeminormedAddCommGroup 𝕜 Fₗ'
  let : NormedSpace 𝕜 Fₗ' := IsNormableSpace.toNormedSpace 𝕜 Fₗ'
  exact ⟨LinearMap.mkContinuous₂ (smulRightLₗ 𝕜 E' Fₗ') 1
    fun c x => by
      first
        | (rw [one_mul]; exact le_of_eq (norm_smulRight_apply c x))
        | simpa only [one_mul] using! (norm_smulRight_apply c x).le,
    fun a b ↦ rfl⟩
