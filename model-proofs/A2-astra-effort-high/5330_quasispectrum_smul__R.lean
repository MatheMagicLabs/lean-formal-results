/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     quasispectrum_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 308
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace PreQuasiregular
variable {R : Type*} [NonUnitalSemiring R]
end PreQuasiregular
namespace Unitization
open PreQuasiregular
variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
variable (R A) in
variable (R) in
end Unitization
section PreQuasiregular
open PreQuasiregular
variable {R : Type*} [NonUnitalSemiring R]
end PreQuasiregular
variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
variable {R} in
variable {R} in
open scoped Pointwise in
variable {R}
open scoped Pointwise in

theorem quasispectrum_smul {R A : Type*} [Semifield R] [NonUnitalRing A] [Module R A]
    (k : R) (a : A) : quasispectrum R (k • a) = k • quasispectrum R a := by
  classical
  have hzero (b : A) : (0 : R) ∈ quasispectrum R b := by
    simp [quasispectrum]
  by_cases hk : k = 0
  · subst k
    ext x
    constructor
    · intro hx
      have hx0 : x = 0 := by
        simpa [quasispectrum, isUnit_iff_ne_zero] using hx
      subst x
      exact ⟨0, hzero a, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hzero (0 : A)
  · have h (x : R) :
        k * x ∈ quasispectrum R (k • a) ↔ x ∈ quasispectrum R a := by
      simp [quasispectrum, Units.smul_def, isUnit_iff_ne_zero,
        smul_smul, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm, hk]
    ext x
    constructor
    · intro hx
      refine ⟨k⁻¹ * x, ?_, ?_⟩
      · apply (h _).mp
        simpa [← mul_assoc, hk] using hx
      · simp [smul_eq_mul, ← mul_assoc, hk]
    · rintro ⟨y, hy, rfl⟩
      exact (h y).mpr hy
