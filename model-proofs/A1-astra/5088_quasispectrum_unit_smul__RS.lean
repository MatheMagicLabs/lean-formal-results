/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     quasispectrum_unit_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 282
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 0 (round 0 = first attempt)
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

theorem quasispectrum_unit_smul (k : Rˣ) (a : A) :
    quasispectrum R (k • a) = k • quasispectrum R a := by
  have hmem (b : A) (r : R) :
      r ∈ quasispectrum R b ↔
        ∀ u : Rˣ, (u : R) = r →
          ¬ IsQuasiregular (-(u⁻¹ • b)) := by
    first
    | rfl
    | change
        (¬ ∃ u : Rˣ, (u : R) = r ∧
          IsQuasiregular (-(u⁻¹ • b))) ↔ _
      simp only [not_exists, not_and]
    | change
        (∀ hr : IsUnit r,
          ¬ IsQuasiregular (-(hr.unit⁻¹ • b))) ↔ _
      constructor
      · intro h u hu
        subst r
        have he : u.isUnit.unit = u :=
          Units.ext u.isUnit.unit_spec
        simpa only [he] using h u.isUnit
      · intro h hr
        exact h hr.unit hr.unit_spec
  ext r
  rw [Set.mem_smul_set_iff_inv_smul_mem, hmem, hmem]
  constructor
  · intro h u hu
    have hu' : ((k * u : Rˣ) : R) = r := by
      change k • (u : R) = r
      rw [hu]
      exact smul_inv_smul k r
    have hh := h (k * u) hu'
    simpa only [mul_inv_rev, mul_smul, inv_smul_smul] using hh
  · intro h u hu
    have hu' : ((k⁻¹ * u : Rˣ) : R) = k⁻¹ • r := by
      change k⁻¹ • (u : R) = k⁻¹ • r
      rw [hu]
    have hh := h (k⁻¹ * u) hu'
    simpa only [mul_inv_rev, inv_inv, mul_smul] using hh
