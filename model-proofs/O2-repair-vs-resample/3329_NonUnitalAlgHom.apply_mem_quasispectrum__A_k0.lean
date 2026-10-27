/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NonUnitalAlgHom.apply_mem_quasispectrum
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 316
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem NonUnitalAlgHom.apply_mem_quasispectrum {F : Type*} [FunLike F A R]
    [NonUnitalAlgHomClass F R A R] [Nontrivial R] (φ : F) (a : A) :
    φ a ∈ quasispectrum R a := by
  intro hr h
  rw [isQuasiregular_iff] at h
  obtain ⟨y, hy₁, -⟩ := h
  have h1 : φ (-(hr.unit⁻¹ • a)) + 1 = 0 := by
    have key : φ (-(hr.unit⁻¹ • a)) + φ (hr.unit⁻¹ • a) = 0 := by
      rw [← map_add, neg_add_cancel, map_zero]
    have h3 : φ (hr.unit⁻¹ • a) = 1 := by
      rw [Units.smul_def, map_smul, smul_eq_mul, IsUnit.val_inv_mul]
    rwa [h3] at key
  have h2 := congr(φ $hy₁)
  rw [map_add, map_add, map_mul, map_zero] at h2
  generalize φ (-(hr.unit⁻¹ • a)) = c at h1 h2
  generalize φ y = d at h2
  have hc : c = 0 := by
    calc c = (1 + c) * d + c := by rw [add_comm 1 c, h1, zero_mul, zero_add]
      _ = d + c + c * d := by rw [add_mul, one_mul, add_right_comm]
      _ = 0 := h2
  rw [hc, zero_add] at h1
  exact one_ne_zero h1
