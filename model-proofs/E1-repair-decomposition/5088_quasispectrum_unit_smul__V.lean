/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     quasispectrum_unit_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 282
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  classical
  ext r
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  change (∀ h : IsUnit r, _) ↔ (∀ h : IsUnit (k⁻¹ • r), _)
  constructor
  · intro h hr
    have hu : IsUnit r := by
      simpa [Units.smul_def, smul_eq_mul, mul_assoc] using k.isUnit.mul hr
    have he : hr.unit = k⁻¹ * hu.unit := by
      apply Units.ext
      simp [hr.unit_spec, hu.unit_spec, Units.smul_def, smul_eq_mul]
    simpa [he, mul_smul, Units.smul_def] using h hu
  · intro h hr
    have hu : IsUnit (k⁻¹ • r) := by
      simpa [Units.smul_def, smul_eq_mul] using k⁻¹.isUnit.mul hr
    have he : hu.unit = k⁻¹ * hr.unit := by
      apply Units.ext
      simp [hu.unit_spec, hr.unit_spec, Units.smul_def, smul_eq_mul]
    simpa [he, mul_smul, Units.smul_def] using h hu
