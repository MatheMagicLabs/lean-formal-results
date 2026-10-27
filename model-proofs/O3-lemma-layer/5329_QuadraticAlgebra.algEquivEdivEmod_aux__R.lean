/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     QuadraticAlgebra.algEquivEdivEmod_aux
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/QuadraticAlgebra/Discriminant.lean, line 185
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
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
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' b
  · have hd : discr a (2 * k) = 4 * (k ^ 2 + a) := by
      simp only [discr]; ring
    have h2 : 2 * k / 2 = k := by omega
    have hq : ∀ X : ℤ, 4 * X / 4 = X := fun X => by omega
    have hr : ∀ X : ℤ, 4 * X % 4 = 0 := fun X => by omega
    rw [hd, h2, hq, hr]
    ring
  · have hd : discr a (2 * k + 1) = 4 * (k ^ 2 + k + a) + 1 := by
      simp only [discr]; ring
    have h2 : (2 * k + 1) / 2 = k := by omega
    have hq : ∀ X : ℤ, (4 * X + 1) / 4 = X := fun X => by omega
    have hr : ∀ X : ℤ, (4 * X + 1) % 4 = 1 := fun X => by omega
    rw [hd, h2, hq, hr]
    ring
