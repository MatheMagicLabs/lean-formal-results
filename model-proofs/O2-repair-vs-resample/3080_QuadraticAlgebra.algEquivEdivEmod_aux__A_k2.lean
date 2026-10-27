/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     QuadraticAlgebra.algEquivEdivEmod_aux
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/QuadraticAlgebra/Discriminant.lean, line 185
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private theorem algEquivEdivEmod_aux {a b : ℤ} :
    a = discr a b / 4 - discr a b % 4 * (b / 2) - (b / 2) ^ 2 := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' b
  · have e1 : (2*k)^2 + 4*a = 4*(k^2+a) := by ring
    have h1 : ∀ m : ℤ, 4*m/4 = m := fun m => by omega
    have h2 : ∀ m : ℤ, 4*m%4 = 0 := fun m => by omega
    have h3 : ∀ m : ℤ, 2*m/2 = m := fun m => by omega
    rw [discr_def, e1, h1, h2, h3]
    ring
  · have e1 : (2*k+1)^2 + 4*a = 4*(k^2+k+a)+1 := by ring
    have h1 : ∀ m : ℤ, (4*m+1)/4 = m := fun m => by omega
    have h2 : ∀ m : ℤ, (4*m+1)%4 = 1 := fun m => by omega
    have h3 : ∀ m : ℤ, (2*m+1)/2 = m := fun m => by omega
    rw [discr_def, e1, h1, h2, h3]
    ring
