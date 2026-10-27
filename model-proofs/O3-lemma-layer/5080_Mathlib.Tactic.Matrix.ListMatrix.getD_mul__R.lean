/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ListMatrix.getD_mul
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/ListMatrix.lean, line 104
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Mathlib.Tactic.Matrix.ListMatrix
variable {α : Type*}

theorem getD_mul [Mul α] [Add α] [Zero α] {l m n i j : Nat} (A B : List (List α)) (hi : i < l)
    (hj : j < n) :
    ((mul l m n A B).getD i []).getD j 0 =
      dotProduct m (A.getD i []) ((transpose n B).getD j []) := by
  unfold mul
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.rightpad]
  by_cases h : i < A.length
  · rw [List.getElem?_append_left h]
    simp [List.getElem?_eq_getElem h, hj]
  · have h3 : A.length ≤ i := by omega
    rw [List.getElem?_append_right h3]
    have h2 : i - A.length < l - A.length := by omega
    simp [List.getElem?_replicate, h2, List.getElem?_eq_none h3, hj]
