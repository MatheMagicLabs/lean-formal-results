/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     QuadraticAlgebra.algEquivEdivEmod_aux
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/QuadraticAlgebra/Discriminant.lean, line 185
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private theorem algEquivEdivEmod_aux {a b : ℤ} :
    a = discr a b / 4 - discr a b % 4 * (b / 2) - (b / 2) ^ 2 := by
  rw [discr_def]
  have h4 : ∀ m : ℤ, 4 * m / 4 = m := by intro m; omega
  have h4' : ∀ m : ℤ, (4 * m + 1) / 4 = m := by intro m; omega
  have h4'' : ∀ m : ℤ, (4 * m + 1) % 4 = 1 := by intro m; omega
  have h0 : ∀ m : ℤ, (4 * m) % 4 = 0 := by intro m; omega
  have h2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases h2 with h | h
  · obtain ⟨q, hq⟩ : ∃ q, b = 2 * q := ⟨b / 2, by omega⟩
    subst hq
    have e1 : (2 * q) ^ 2 + 4 * a = 4 * (a + q ^ 2) := by ring
    have e2 : 2 * q / 2 = q := by omega
    rw [e1, e2, h4, h0]
    ring
  · obtain ⟨q, hq⟩ : ∃ q, b = 2 * q + 1 := ⟨b / 2, by omega⟩
    subst hq
    have e1 : (2 * q + 1) ^ 2 + 4 * a = 4 * (a + q ^ 2 + q) + 1 := by ring
    have e2 : (2 * q + 1) / 2 = q := by omega
    rw [e1, e2, h4', h4'']
    ring
