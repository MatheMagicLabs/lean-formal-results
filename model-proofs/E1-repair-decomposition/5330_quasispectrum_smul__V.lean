/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     quasispectrum_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 308
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
variable {R}
open scoped Pointwise in

theorem quasispectrum_smul {R A : Type*} [Semifield R] [NonUnitalRing A] [Module R A]
    (k : R) (a : A) : quasispectrum R (k • a) = k • quasispectrum R a := by
  classical
  have hunit (r : R) (hr : IsUnit r) (b : A) :
      hr.unit⁻¹ • b = r⁻¹ • b := by
    change (↑(hr.unit⁻¹) : R) • b = _
    rw [Units.val_inv_eq_inv_val, hr.unit_spec]
  by_cases hk : k = 0
  · subst k
    ext r
    simp [quasispectrum, Set.mem_smul_set, isUnit_iff_ne_zero]
    constructor
    · intro hr
      exact ⟨⟨0, by simp⟩, hr.symm⟩
    · intro hr
      exact hr.2.symm
  · ext r
    change r ∈ quasispectrum R (k • a) ↔
      ∃ s ∈ quasispectrum R a, k * s = r
    constructor
    · intro hr
      refine ⟨k⁻¹ * r, ?_, by simp [hk]⟩
      simpa [quasispectrum, hunit, isUnit_iff_ne_zero,
        smul_smul, smul_neg, hk, mul_inv_rev,
        mul_comm, mul_left_comm, mul_assoc] using hr
    · rintro ⟨s, hs, rfl⟩
      simpa [quasispectrum, hunit, isUnit_iff_ne_zero,
        smul_smul, smul_neg, hk, mul_inv_rev,
        mul_comm, mul_left_comm, mul_assoc] using hs
