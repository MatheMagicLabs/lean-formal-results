/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     quasispectrum_unit_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 282
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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

theorem quasispectrum_unit_smul (k : Rˣ) (a : A) :
    quasispectrum R (k • a) = k • quasispectrum R a := by
  ext r
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  by_cases hr : IsUnit r
  · obtain ⟨r, rfl⟩ := hr
    have h : (k⁻¹ • (r : R)) = ((k⁻¹ * r : Rˣ) : R) := by
      rw [Units.smul_def, smul_eq_mul, Units.val_mul]
    rw [h, quasispectrum.units_mem_iff, quasispectrum.units_mem_iff]
    simp only [mul_inv_rev, inv_inv, mul_smul]
  · have h : ¬ IsUnit (k⁻¹ • r) := by
      rwa [Units.smul_def, smul_eq_mul, Units.isUnit_units_mul]
    exact iff_of_true (quasispectrum.not_isUnit_mem _ hr)
      (quasispectrum.not_isUnit_mem _ h)
