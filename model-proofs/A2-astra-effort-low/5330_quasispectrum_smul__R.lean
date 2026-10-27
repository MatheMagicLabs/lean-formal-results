/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     quasispectrum_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 308
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  by_cases hk : k = 0
  · subst k
    ext x
    change x ∈ quasispectrum R (0 • a) ↔
      ∃ y ∈ quasispectrum R a, (0 : R) * y = x
    constructor
    · intro hx
      have hx0 : x = 0 := by
        simpa [quasispectrum, isUnit_iff_ne_zero] using hx
      subst x
      exact ⟨0, by simp [quasispectrum], zero_mul 0⟩
    · rintro ⟨y, hy, hxy⟩
      have hx0 : x = 0 := by simpa using hxy.symm
      subst x
      simp [quasispectrum]
  · have h (y : R) :
        k * y ∈ quasispectrum R (k • a) ↔
          y ∈ quasispectrum R a := by
      simp [quasispectrum, Units.smul_def, Units.val_inv_eq_inv_val,
        isUnit_iff_ne_zero, hk, smul_smul, mul_inv_rev,
        mul_assoc, mul_comm, mul_left_comm]
    ext x
    change x ∈ quasispectrum R (k • a) ↔
      ∃ y ∈ quasispectrum R a, k * y = x
    constructor
    · intro hx
      have he : k * (k⁻¹ * x) = x := by
        rw [← mul_assoc, mul_inv_cancel₀ hk, one_mul]
      exact ⟨k⁻¹ * x, (h _).mp (he.symm ▸ hx), he⟩
    · rintro ⟨y, hy, rfl⟩
      exact (h y).mpr hy
