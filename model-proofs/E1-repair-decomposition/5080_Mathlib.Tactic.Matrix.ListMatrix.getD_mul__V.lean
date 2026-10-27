/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ListMatrix.getD_mul
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/ListMatrix.lean, line 104
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Mathlib.Tactic.Matrix.ListMatrix
variable {α : Type*}

theorem getD_mul [Mul α] [Add α] [Zero α] {l m n i j : Nat} (A B : List (List α)) (hi : i < l)
    (hj : j < n) :
    ((mul l m n A B).getD i []).getD j 0 =
      dotProduct m (A.getD i []) ((transpose n B).getD j []) := by
  have h : ∀ (xs : List (List α)) (r k : Nat), k < r →
      (xs.map (fun row => (transpose n B).map (dotProduct m row)) ++
        List.replicate (r - xs.length)
          ((transpose n B).map (dotProduct m []))).getD k [] =
      (transpose n B).map (dotProduct m (xs.getD k [])) := by
    intro xs
    induction xs with
    | nil =>
        intro r k hk
        simp [List.getD, hk]
    | cons x xs ih =>
        intro r k hk
        cases k with
        | zero => simp [List.getD]
        | succ k =>
            cases r with
            | zero => omega
            | succ r =>
                simpa [List.getD, Nat.succ_sub_succ] using
                  ih r k (Nat.lt_of_succ_lt_succ hk)
  simpa [mul, List.getD, hi, hj] using
    congrArg (fun row : List α => row.getD j 0) (h A l i hi)
