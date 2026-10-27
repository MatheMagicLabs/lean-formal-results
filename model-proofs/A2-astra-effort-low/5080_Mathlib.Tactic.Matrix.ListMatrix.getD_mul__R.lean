/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ListMatrix.getD_mul
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/ListMatrix.lean, line 104
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Mathlib.Tactic.Matrix.ListMatrix
variable {α : Type*}

theorem getD_mul [Mul α] [Add α] [Zero α] {l m n i j : Nat} (A B : List (List α)) (hi : i < l)
    (hj : j < n) :
    ((mul l m n A B).getD i []).getD j 0 =
      dotProduct m (A.getD i []) ((transpose n B).getD j []) := by
  have h (xs : List (List α)) (f : List α → List α)
      (d e : List α) (t k : Nat) (hk : k < t) :
      (xs.map f ++ List.replicate (t - xs.length) (f d)).getD k e =
        f (xs.getD k d) := by
    induction k generalizing xs t with
    | zero =>
        cases t <;> cases xs <;>
          simp_all [List.getD, List.replicate_succ]
    | succ k ih =>
        cases t <;> cases xs <;>
          simp_all [List.getD, List.replicate_succ]
  simp only [mul, List.rightpad, List.map_append, List.map_replicate]
  rw [h A (fun row => (transpose n B).map (dotProduct m row)) [] [] l i hi]
  simp [List.getD, hj]
