/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     QuadraticAlgebra.algEquivEdivEmod_aux
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/QuadraticAlgebra/Discriminant.lean, line 185
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private theorem algEquivEdivEmod_aux {a b : ℤ} :
    a = discr a b / 4 - discr a b % 4 * (b / 2) - (b / 2) ^ 2 := by
  obtain ⟨q, r, hb, hr⟩ : ∃ q r : ℤ, b = 2 * q + r ∧ (r = 0 ∨ r = 1) :=
    ⟨b / 2, b % 2, by omega, by omega⟩
  have hd : discr a b = 4 * (q ^ 2 + q * r + a) + r := by
    rw [discr_def, hb]
    rcases hr with rfl | rfl <;> ring
  have h2 : b / 2 = q := by omega
  rw [hd, h2]
  have h4 : (4 * (q ^ 2 + q * r + a) + r) / 4 = q ^ 2 + q * r + a := by omega
  have h5 : (4 * (q ^ 2 + q * r + a) + r) % 4 = r := by omega
  rw [h4, h5]
  ring
