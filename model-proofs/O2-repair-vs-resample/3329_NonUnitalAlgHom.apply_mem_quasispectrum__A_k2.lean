/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NonUnitalAlgHom.apply_mem_quasispectrum
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 316
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem NonUnitalAlgHom.apply_mem_quasispectrum {F : Type*} [FunLike F A R]
    [NonUnitalAlgHomClass F R A R] [Nontrivial R] (φ : F) (a : A) :
    φ a ∈ quasispectrum R a := by
  intro hr hq
  have h1 : φ (hr.unit⁻¹ • a) = 1 := by
    rw [Units.smul_def, map_smul, smul_eq_mul, hr.val_inv_mul]
  have h2 : φ (-(hr.unit⁻¹ • a)) + 1 = 0 := by
    rw [← h1, ← map_add, neg_add_cancel, map_zero]
  obtain ⟨y, hy1, hy2⟩ := isQuasiregular_iff.mp (hq.map φ)
  have hx : φ (-(hr.unit⁻¹ • a)) = 0 := by
    calc φ (-(hr.unit⁻¹ • a))
        = φ (-(hr.unit⁻¹ • a)) + (φ (-(hr.unit⁻¹ • a)) + 1) * y := by
          rw [h2, zero_mul, add_zero]
      _ = y + φ (-(hr.unit⁻¹ • a)) + φ (-(hr.unit⁻¹ • a)) * y := by ring
      _ = 0 := hy1
  rw [hx, zero_add] at h2
  exact one_ne_zero h2
