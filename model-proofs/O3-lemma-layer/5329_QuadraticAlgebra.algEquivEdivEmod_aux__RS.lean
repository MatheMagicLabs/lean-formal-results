/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     QuadraticAlgebra.algEquivEdivEmod_aux
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/QuadraticAlgebra/Discriminant.lean, line 185
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace QuadraticAlgebra
variable {R : Type*}
section discr
end discr
section classification
variable [CommRing R] {a b a' b' : R}
section Int

private theorem algEquivEdivEmod_aux {a b : ℤ} :
    a = discr a b / 4 - discr a b % 4 * (b / 2) - (b / 2) ^ 2 := by
  rw [discr_def]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1) ∧ b = 2 * q + r :=
    ⟨b / 2, b % 2, by omega, by omega⟩
  rcases hr with rfl | rfl
  · have h1 : (2 * q + 0) / 2 = q := by omega
    have h2 : (2 * q + 0) ^ 2 + 4 * a = 0 + (q ^ 2 + a) * 4 := by ring
    rw [h1, h2, Int.add_mul_ediv_right _ _ (by norm_num : (4:ℤ) ≠ 0),
      Int.add_mul_emod_self_right]
    norm_num <;> ring
  · have h1 : (2 * q + 1) / 2 = q := by omega
    have h2 : (2 * q + 1) ^ 2 + 4 * a = 1 + (q ^ 2 + q + a) * 4 := by ring
    rw [h1, h2, Int.add_mul_ediv_right _ _ (by norm_num : (4:ℤ) ≠ 0),
      Int.add_mul_emod_self_right]
    norm_num <;> ring
