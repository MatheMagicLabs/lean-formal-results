/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NonUnitalAlgHom.apply_mem_quasispectrum
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 316
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem NonUnitalAlgHom.apply_mem_quasispectrum {F : Type*} [FunLike F A R]
    [NonUnitalAlgHomClass F R A R] [Nontrivial R] (φ : F) (a : A) :
    φ a ∈ quasispectrum R a := by
  intro hu h
  obtain ⟨z, hz₁, -⟩ := isQuasiregular_iff.mp (h.map φ)
  have h2 : φ (hu.unit⁻¹ • a) = 1 := by
    rw [Units.smul_def, map_smul, smul_eq_mul]
    exact hu.val_inv_mul
  have hy : φ (-(hu.unit⁻¹ • a)) + 1 = 0 := by
    rw [← h2, ← map_add, neg_add_cancel, map_zero]
  generalize φ (-(hu.unit⁻¹ • a)) = y at hy hz₁
  have h3 : z * y + z = 0 := by
    have := congr_arg (z * ·) hy
    simpa [mul_add] using this
  have h4 : y = 0 := by
    calc y = y + (z * y + z) := by rw [h3, add_zero]
      _ = z + y + y * z := by rw [mul_comm z y]; abel
      _ = 0 := hz₁
  exact one_ne_zero (by rw [← hy, h4, zero_add])
