/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     QuadraticAlgebra.algEquivEdivEmod_aux
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/QuadraticAlgebra/Discriminant.lean, line 185
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm N0, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  let q := b / 2
  change a = discr a b / 4 - discr a b % 4 * q - q ^ 2
  have hb : b = 2 * q + b % 2 := by
    dsimp [q]
    omega
  have hr : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases hr with hr | hr
  · have hd : discr a b = 4 * (a + q ^ 2) := by
      unfold discr
      rw [hb, hr]
      ring
    have hm : discr a b % 4 = 0 := by omega
    have hq : discr a b / 4 = a + q ^ 2 := by omega
    rw [hm, hq]
    ring
  · have hd : discr a b = 4 * (a + q ^ 2 + q) + 1 := by
      unfold discr
      rw [hb, hr]
      ring
    have hm : discr a b % 4 = 1 := by omega
    have hq : discr a b / 4 = a + q ^ 2 + q := by omega
    rw [hm, hq]
    ring
