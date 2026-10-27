/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ListMatrix.getD_mul
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/ListMatrix.lean, line 104
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Mathlib.Tactic.Matrix.ListMatrix
variable {α : Type*}

theorem getD_mul [Mul α] [Add α] [Zero α] {l m n i j : Nat} (A B : List (List α)) (hi : i < l)
    (hj : j < n) :
    ((mul l m n A B).getD i []).getD j 0 =
      dotProduct m (A.getD i []) ((transpose n B).getD j []) := by
  induction A generalizing l i with
  | nil =>
      simp [mul, List.getD, hi, hj]
  | cons a A ih =>
      cases i with
      | zero =>
          simp [mul, List.getD, hj]
      | succ i =>
          cases l with
          | zero => omega
          | succ l =>
              simpa [mul, List.getD, Nat.succ_sub_succ_eq_sub] using
                (ih (l := l) (i := i) (Nat.lt_of_succ_lt_succ hi))
