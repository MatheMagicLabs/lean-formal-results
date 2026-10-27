/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     QuadraticAlgebra.algEquivEdivEmod_aux
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/QuadraticAlgebra/Discriminant.lean, line 185
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private theorem algEquivEdivEmod_aux {a b : ℤ} :
    a = discr a b / 4 - discr a b % 4 * (b / 2) - (b / 2) ^ 2 := by
  rcases Int.emod_two_eq_zero_or_one b with h | h
  · obtain ⟨q, hq⟩ : ∃ q, b = 2 * q := ⟨b / 2, by omega⟩
    subst hq
    have h2 : 2 * q / 2 = q := by omega
    have hD : discr a (2 * q) = 4 * (q ^ 2 + a) := by rw [discr_def]; ring
    rw [h2, hD]
    have h3 : 4 * (q ^ 2 + a) / 4 = q ^ 2 + a := by omega
    have h4 : 4 * (q ^ 2 + a) % 4 = 0 := by omega
    rw [h3, h4]; ring
  · obtain ⟨q, hq⟩ : ∃ q, b = 2 * q + 1 := ⟨b / 2, by omega⟩
    subst hq
    have h2 : (2 * q + 1) / 2 = q := by omega
    have hD : discr a (2 * q + 1) = 4 * (q ^ 2 + q + a) + 1 := by rw [discr_def]; ring
    rw [h2, hD]
    have h3 : (4 * (q ^ 2 + q + a) + 1) / 4 = q ^ 2 + q + a := by omega
    have h4 : (4 * (q ^ 2 + q + a) + 1) % 4 = 1 := by omega
    rw [h3, h4]; ring
