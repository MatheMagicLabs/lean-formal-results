/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ListMatrix.getD_transpose
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/ListMatrix.lean, line 83
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Mathlib.Tactic.Matrix.ListMatrix
variable {α : Type*}

theorem getD_transpose [Zero α] {n j : Nat} (rows : List (List α)) (i : Nat) (hj : j < n) :
    ((transpose n rows).getD j []).getD i 0 = (rows.getD i []).getD j 0 := by
  have hlen (xs : List α) (ys : List (List α)) :
      ys.length ≤ (consPad xs ys).length := by
    induction ys generalizing xs with
    | nil => simp
    | cons y ys ih =>
      cases xs <;> simp_all [consPad]
  have hget (xs : List α) (ys : List (List α)) (k : Nat)
      (hk : k < ys.length) :
      (consPad xs ys).getD k [] =
        xs.getD k 0 :: ys.getD k [] := by
    induction ys generalizing xs k with
    | nil => simp_all
    | cons y ys ih =>
      cases xs <;> cases k <;> simp_all [consPad, List.getD]
  have ht (rs : List (List α)) : n ≤ (transpose n rs).length := by
    induction rs with
    | nil => simp [transpose]
    | cons r rs ih =>
      exact Nat.le_trans ih (hlen r (transpose n rs))
  induction rows generalizing i with
  | nil =>
    simp [transpose, List.getD, hj]
  | cons row rows ih =>
    change ((consPad row (transpose n rows)).getD j []).getD i 0 =
      ((row :: rows).getD i []).getD j 0
    rw [hget row (transpose n rows) j (Nat.lt_of_lt_of_le hj (ht rows))]
    cases i with
    | zero => simp [List.getD]
    | succ i => simpa [List.getD] using ih i
