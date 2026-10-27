/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NonUnitalAlgHom.apply_mem_quasispectrum
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 316
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
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
    have h0 : φ (-(hr.unit⁻¹ • a)) + φ (hr.unit⁻¹ • a) = 0 := by
      rw [← map_add, neg_add_cancel, map_zero]
    have h2 : φ (hr.unit⁻¹ • a) = 1 := by
      rw [Units.smul_def, map_smul, smul_eq_mul]
      exact hr.val_inv_mul
    rwa [h2] at h0
  have h3 := congr(φ $hy₁)
  rw [map_add, map_add, map_mul, map_zero] at h3
  have key : (1 + φ (-(hr.unit⁻¹ • a))) * (1 + φ y) = 1 := by
    calc (1 + φ (-(hr.unit⁻¹ • a))) * (1 + φ y)
        = 1 + (φ y + φ (-(hr.unit⁻¹ • a)) + φ (-(hr.unit⁻¹ • a)) * φ y) := by ring
      _ = 1 := by rw [h3, add_zero]
  rw [add_comm (1 : R), h1, zero_mul] at key
  exact zero_ne_one key
