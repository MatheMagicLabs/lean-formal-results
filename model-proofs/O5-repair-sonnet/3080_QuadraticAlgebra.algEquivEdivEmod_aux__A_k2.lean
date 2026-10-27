/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     QuadraticAlgebra.algEquivEdivEmod_aux
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/QuadraticAlgebra/Discriminant.lean, line 185
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private theorem algEquivEdivEmod_aux {a b : ℤ} :
    a = discr a b / 4 - discr a b % 4 * (b / 2) - (b / 2) ^ 2 := by
  obtain ⟨q, r, hr, hb⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1) ∧ b = 2 * q + r :=
    ⟨b / 2, b % 2, by omega, by omega⟩
  subst hb
  have hq : (2 * q + r) / 2 = q := by omega
  rcases hr with rfl | rfl
  · have h : discr a (2 * q + 0) = 4 * (q ^ 2 + a) := by rw [discr_def]; ring
    have h1 : 4 * (q ^ 2 + a) / 4 = q ^ 2 + a := by omega
    have h2 : 4 * (q ^ 2 + a) % 4 = 0 := by omega
    rw [h, hq, h1, h2]
    ring
  · have h : discr a (2 * q + 1) = 4 * (q ^ 2 + q + a) + 1 := by rw [discr_def]; ring
    have h1 : (4 * (q ^ 2 + q + a) + 1) / 4 = q ^ 2 + q + a := by omega
    have h2 : (4 * (q ^ 2 + q + a) + 1) % 4 = 1 := by omega
    rw [h, hq, h1, h2]
    ring
