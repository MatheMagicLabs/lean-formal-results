/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     QuadraticAlgebra.algEquivEdivEmod_aux
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/QuadraticAlgebra/Discriminant.lean, line 185
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  have he : b = 2 * (b / 2) + b % 2 := by omega
  have hs := congrArg (fun x : ℤ => x ^ 2) he
  have hd :
      discr a b =
        4 * (a + (b / 2) ^ 2 + (b / 2) * (b % 2)) + (b % 2) ^ 2 := by
    dsimp [discr]
    nlinarith [hs]
  have hdiv : discr a b = discr a b % 4 + 4 * (discr a b / 4) := by
    omega
  have hlo := Int.emod_nonneg (discr a b) (by norm_num : (4 : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos (discr a b) (by norm_num : (0 : ℤ) < 4)
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases hb with hb | hb
  all_goals
    rw [hb] at hd
    norm_num at hd
    have hr : discr a b % 4 = b % 2 := by omega
    rw [hr, hb]
    nlinarith
