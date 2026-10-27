/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ListMatrix.getD_transpose
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/ListMatrix.lean, line 83
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Mathlib.Tactic.Matrix.ListMatrix
variable {α : Type*}

theorem getD_transpose [Zero α] {n j : Nat} (rows : List (List α)) (i : Nat) (hj : j < n) :
    ((transpose n rows).getD j []).getD i 0 = (rows.getD i []).getD j 0 := by
  have hcons (row : List α) (cols : List (List α)) (k : Nat)
      (hk : k < cols.length) :
      (consPad row cols).getD k [] =
        row.getD k 0 :: cols.getD k [] := by
    induction cols generalizing row k with
    | nil =>
        simp at hk
    | cons col cols ih =>
        cases row <;> cases k <;>
          simp_all [consPad, List.getD]
  induction rows generalizing i with
  | nil =>
      simp [transpose, List.getD, hj]
  | cons row rows ih =>
      rw [transpose, hcons row (transpose n rows) j (by simpa using hj)]
      cases i <;> simp_all [List.getD]
