/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     quasispectrum_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 308
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm B, verified in round 2 (round 0 = first attempt)
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
variable {R}
open scoped Pointwise in

theorem quasispectrum_smul {R A : Type*} [Semifield R] [NonUnitalRing A] [Module R A]
    (k : R) (a : A) : quasispectrum R (k • a) = k • quasispectrum R a := by
  classical
  by_cases hk : k = 0
  · subst k
    have h0 : (0 : R) ∈ quasispectrum R a := by
      simp [quasispectrum]
    ext r
    constructor
    · intro hr
      have hr0 : r = 0 := by
        simpa [quasispectrum, Units.smul_def, isUnit_iff_ne_zero] using hr
      subst r
      exact ⟨0, h0, by simp⟩
    · rintro ⟨s, hs, rfl⟩
      simp [quasispectrum]
  · ext r
    constructor
    · intro hr
      refine ⟨k⁻¹ * r, ?_, by simp [hk]⟩
      simpa [quasispectrum, Units.smul_def, Ring.inverse_eq_inv,
        Units.val_inv_eq_inv_val, isUnit_iff_ne_zero,
        smul_smul, smul_neg, hk, mul_comm, mul_left_comm, mul_assoc] using hr
    · rintro ⟨s, hs, rfl⟩
      simpa [quasispectrum, Units.smul_def, Ring.inverse_eq_inv,
        Units.val_inv_eq_inv_val, isUnit_iff_ne_zero,
        smul_smul, smul_neg, hk, mul_comm, mul_left_comm, mul_assoc] using hs
