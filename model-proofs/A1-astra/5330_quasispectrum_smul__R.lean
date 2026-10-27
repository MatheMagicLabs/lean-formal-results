/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     quasispectrum_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 308
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
    apply Set.Subset.antisymm
    · intro r hr
      have hr0 : r = 0 := by simpa using hr
      subst r
      exact ⟨0, by simp, by simp⟩
    · rintro r ⟨s, hs, rfl⟩
      simp
  ext r
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hk]
  by_cases hr : r = 0
  · subst r
    simp
  · simp [quasispectrum, Units.smul_def, Units.val_inv_eq_inv_val,
      smul_eq_mul, isUnit_iff_ne_zero, hk, hr, smul_smul,
      mul_comm, mul_left_comm, mul_assoc]
