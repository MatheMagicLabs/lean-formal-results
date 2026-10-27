/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     quasispectrum_unit_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 282
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
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
  ext r
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp only [quasispectrum, Set.mem_setOf_eq]
  refine ⟨fun h hr => ?_, fun h hr => ?_⟩
  · have hr' : IsUnit r := by
      have := k.isUnit.mul hr
      rwa [Units.smul_def, smul_eq_mul, ← mul_assoc, Units.mul_inv, one_mul] at this
    have e : hr.unit⁻¹ • a = hr'.unit⁻¹ • k • a := by
      rw [smul_smul]
      congr 1
      rw [← inv_inj, mul_inv_rev, inv_inv, inv_inv]
      ext
      simp [Units.smul_def, smul_eq_mul]
    rw [e]
    exact h hr'
  · have hr' : IsUnit (k⁻¹ • r) := by
      rw [Units.smul_def, smul_eq_mul]
      exact (k⁻¹).isUnit.mul hr
    have e : hr.unit⁻¹ • k • a = hr'.unit⁻¹ • a := by
      rw [smul_smul]
      congr 1
      rw [← inv_inj, mul_inv_rev, inv_inv, inv_inv]
      ext
      simp [Units.smul_def, smul_eq_mul]
    rw [e]
    exact h hr'
