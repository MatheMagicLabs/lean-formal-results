/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     QuadraticAlgebra.algEquivEdivEmod_aux
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/QuadraticAlgebra/Discriminant.lean, line 185
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private theorem algEquivEdivEmod_aux {a b : ℤ} :
    a = discr a b / 4 - discr a b % 4 * (b / 2) - (b / 2) ^ 2 := by
  rcases Int.even_or_odd' b with ⟨k, rfl | rfl⟩
  · have h1 : discr a (2 * k) = 4 * (k ^ 2 + a) := by rw [discr_def]; ring
    rw [h1]
    have h2 : (2 * k) / 2 = k := by omega
    have h3 : (4 * (k ^ 2 + a)) / 4 = k ^ 2 + a := by
      generalize k ^ 2 + a = m; omega
    have h4 : (4 * (k ^ 2 + a)) % 4 = 0 := by
      generalize k ^ 2 + a = m; omega
    rw [h2, h3, h4]; ring
  · have h1 : discr a (2 * k + 1) = 4 * (k ^ 2 + k + a) + 1 := by rw [discr_def]; ring
    rw [h1]
    have h2 : (2 * k + 1) / 2 = k := by omega
    have h3 : (4 * (k ^ 2 + k + a) + 1) / 4 = k ^ 2 + k + a := by
      generalize k ^ 2 + k + a = m; omega
    have h4 : (4 * (k ^ 2 + k + a) + 1) % 4 = 1 := by
      generalize k ^ 2 + k + a = m; omega
    rw [h2, h3, h4]; ring
