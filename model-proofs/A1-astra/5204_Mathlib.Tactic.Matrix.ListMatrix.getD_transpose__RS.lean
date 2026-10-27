/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ListMatrix.getD_transpose
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/ListMatrix.lean, line 83
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
    | nil => simp at hk
    | cons col cols ih =>
      cases row with
      | nil =>
        cases k with
        | zero => simp [consPad]
        | succ k =>
          simpa [consPad] using
            ih [] k (Nat.lt_of_succ_lt_succ hk)
      | cons a row =>
        cases k with
        | zero => simp [consPad]
        | succ k =>
          simpa [consPad] using
            ih row k (Nat.lt_of_succ_lt_succ hk)
  have hr (m k : Nat) :
      (List.replicate m ([] : List α)).getD k [] = [] := by
    induction m generalizing k with
    | zero => simp
    | succ m ih =>
      cases k with
      | zero => simp [List.replicate_succ]
      | succ k =>
        simpa [List.replicate_succ] using ih k
  induction rows generalizing i with
  | nil =>
    simp only [transpose, hr]
    simp
  | cons row rows ih =>
    have ht :
        (transpose n (row :: rows)).getD j [] =
          row.getD j 0 :: (transpose n rows).getD j [] := by
      change (consPad row (transpose n rows)).getD j [] = _
      exact hcons row (transpose n rows) j
        (by simpa only [length_transpose] using hj)
    rw [ht]
    cases i with
    | zero => simp
    | succ i => simpa using ih i
