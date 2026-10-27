/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     QuadraticAlgebra.algEquivEdivEmod_aux
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/QuadraticAlgebra/Discriminant.lean, line 185
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private theorem algEquivEdivEmod_aux {a b : ℤ} :
    a = discr a b / 4 - discr a b % 4 * (b / 2) - (b / 2) ^ 2 := by
  have hb : b = 2 * (b / 2) + b % 2 := by omega
  rcases Int.emod_two_eq_zero_or_one b with h | h
  · generalize b / 2 = q at hb ⊢
    rw [h] at hb
    have hd : discr a b = 4 * (q ^ 2 + a) + 0 := by
      rw [discr_def, hb]; ring
    generalize discr a b = D at hd
    have h1 : D / 4 = q ^ 2 + a := by omega
    have h2 : D % 4 = 0 := by omega
    rw [h1, h2]
    ring
  · generalize b / 2 = q at hb ⊢
    rw [h] at hb
    have hd : discr a b = 4 * (q ^ 2 + q + a) + 1 := by
      rw [discr_def, hb]; ring
    generalize discr a b = D at hd
    have h1 : D / 4 = q ^ 2 + q + a := by omega
    have h2 : D % 4 = 1 := by omega
    rw [h1, h2]
    ring
