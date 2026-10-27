/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     quasispectrum_unit_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 282
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
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

theorem quasispectrum_unit_smul (k : Rˣ) (a : A) :
    quasispectrum R (k • a) = k • quasispectrum R a := by
  classical
  ext r
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  by_cases hr : IsUnit r
  · rcases hr with ⟨u, rfl⟩
    have hunit (v : Rˣ) (hv : IsUnit (v : R)) : hv.unit = v := by
      apply Units.ext
      exact hv.unit_spec
    change (u : R) ∈ quasispectrum R (k • a) ↔
      ((k⁻¹ * u : Rˣ) : R) ∈ quasispectrum R a
    simp only [quasispectrum, Set.mem_setOf_eq, hunit]
    simp [mul_smul]
  · have hr' : ¬ IsUnit (k⁻¹ • r) := by
      intro h
      have h' : IsUnit (k • (k⁻¹ • r)) := k.isUnit.mul h
      exact hr (by simpa using h')
    have hru (u : Rˣ) : (u : R) ≠ r :=
      fun h => hr (h ▸ u.isUnit)
    have hru' (u : Rˣ) : (u : R) ≠ k⁻¹ • r :=
      fun h => hr' (h ▸ u.isUnit)
    simp [quasispectrum, hr, hr', hru, hru']
