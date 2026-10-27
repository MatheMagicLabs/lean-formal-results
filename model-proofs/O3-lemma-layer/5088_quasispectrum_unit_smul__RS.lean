/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     quasispectrum_unit_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 282
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  by_cases hx : IsUnit x
  · lift x to Rˣ using hx
    have key : k⁻¹ • (x : R) = ((k⁻¹ * x : Rˣ) : R) := rfl
    rw [key, quasispectrum.units_mem_iff, quasispectrum.units_mem_iff, mul_inv_rev, inv_inv,
      mul_smul] <;> rfl
  · have h2 : ¬ IsUnit (k⁻¹ • x) := by
      rw [show k⁻¹ • x = ((k⁻¹ : Rˣ) : R) * x from rfl, Units.isUnit_units_mul]
      exact hx
    exact iff_of_true (fun h => absurd h hx) (fun h => absurd h h2)
