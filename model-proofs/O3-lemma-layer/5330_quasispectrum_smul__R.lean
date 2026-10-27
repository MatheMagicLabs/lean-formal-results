/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     quasispectrum_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 308
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
variable {R}
open scoped Pointwise in

theorem quasispectrum_smul {R A : Type*} [Semifield R] [NonUnitalRing A] [Module R A]
    (k : R) (a : A) : quasispectrum R (k • a) = k • quasispectrum R a := by
  have key : ∀ (b : A) (r : R), r ∈ quasispectrum R b ↔
      (r ≠ 0 → ¬ IsQuasiregular (-(r⁻¹ • b))) := by
    intro b r
    constructor
    · intro h hr
      have := h (isUnit_iff_ne_zero.mpr hr)
      simpa [Units.smul_def] using this
    · intro h hr
      simpa [Units.smul_def] using h hr.ne_zero
  rcases eq_or_ne k 0 with rfl | hk
  · ext r
    rw [zero_smul, Set.zero_smul_set ⟨0, quasispectrum.zero_mem (R := R) a⟩]
    rw [Set.mem_zero, key]
    constructor
    · intro h
      by_contra hr
      apply h hr
      rw [smul_zero, neg_zero]
      first
        | exact isQuasiregular_zero
        | exact ⟨1, rfl⟩
    · rintro rfl h
      exact absurd rfl h
  · ext r
    rw [key, Set.mem_smul_set_iff_inv_smul_mem₀ hk, key, smul_eq_mul]
    first
      | (simp only [ne_eq, mul_eq_zero, inv_eq_zero, hk, false_or, mul_inv_rev, inv_inv,
          smul_smul]; done)
      | simp [hk, smul_smul]
