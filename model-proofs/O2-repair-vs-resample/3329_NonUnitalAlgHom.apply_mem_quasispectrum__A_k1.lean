/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NonUnitalAlgHom.apply_mem_quasispectrum
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 316
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
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
  rw [isQuasiregular_iff] at hq
  obtain ⟨y, hy₁, -⟩ := hq
  set c := -(hr.unit⁻¹ • a) with hc
  have hb : φ (hr.unit⁻¹ • a) = 1 := by
    rw [Units.smul_def, map_smul, smul_eq_mul]
    exact hr.val_inv_mul
  have h2 : φ c + 1 = 0 := by
    rw [← hb, ← map_add, hc, neg_add_cancel, map_zero]
  have h1 : φ y + φ c + φ c * φ y = 0 := by
    have := congr(φ $hy₁)
    rwa [map_add, map_add, map_mul, map_zero] at this
  have h3 : (φ c + 1) * (φ y + 1) = 1 := by
    calc (φ c + 1) * (φ y + 1) = (φ y + φ c + φ c * φ y) + 1 := by ring
    _ = 1 := by rw [h1, zero_add]
  rw [h2, zero_mul] at h3
  exact zero_ne_one h3
