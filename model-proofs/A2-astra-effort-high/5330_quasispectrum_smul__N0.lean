/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     quasispectrum_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 308
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm N0, verified in round 0 (round 0 = first attempt)
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
  by_cases hk : k = 0
  · subst k
    have hz : (0 : R) ∈ quasispectrum R a := by
      simp [quasispectrum]
    ext r
    change r ∈ quasispectrum R (0 • a) ↔
      ∃ s ∈ quasispectrum R a, (0 : R) • s = r
    simp only [zero_smul]
    constructor
    · intro hr
      have hr0 : r = 0 := by
        simpa [quasispectrum] using hr
      subst r
      exact ⟨0, hz, rfl⟩
    · rintro ⟨s, hs, hr⟩
      rw [← hr]
      simp [quasispectrum]
  · have h (r : R) :
        r ∈ quasispectrum R (k • a) ↔
          k⁻¹ * r ∈ quasispectrum R a := by
      by_cases hr : r = 0
      · simp [hr, quasispectrum]
      · simp [quasispectrum, hk, hr, Units.smul_def, mul_inv_rev,
          smul_smul, mul_comm, mul_left_comm, mul_assoc]
    ext r
    change r ∈ quasispectrum R (k • a) ↔
      ∃ s ∈ quasispectrum R a, k • s = r
    constructor
    · intro hr
      refine ⟨k⁻¹ * r, (h r).mp hr, ?_⟩
      simp [smul_eq_mul, ← mul_assoc, hk]
    · rintro ⟨s, hs, rfl⟩
      apply (h _).mpr
      simpa [smul_eq_mul, ← mul_assoc, hk] using hs
