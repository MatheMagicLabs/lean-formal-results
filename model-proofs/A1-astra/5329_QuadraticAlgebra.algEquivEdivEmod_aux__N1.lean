/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     QuadraticAlgebra.algEquivEdivEmod_aux
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/QuadraticAlgebra/Discriminant.lean, line 185
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm N1, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  have hb : b = 2 * (b / 2) + b % 2 := by omega
  have hr : b % 2 = 0 ∨ b % 2 = 1 := by omega
  have hd : discr a b =
      4 * (a + (b / 2) ^ 2 + (b % 2) * (b / 2)) + b % 2 := by
    unfold discr
    conv_lhs => rw [hb]
    rcases hr with hr | hr <;> simp only [hr] <;> ring
  have hm : discr a b % 4 = b % 2 := by omega
  have hq : discr a b / 4 =
      a + (b / 2) ^ 2 + (b % 2) * (b / 2) := by omega
  rw [hm, hq]
  ring
