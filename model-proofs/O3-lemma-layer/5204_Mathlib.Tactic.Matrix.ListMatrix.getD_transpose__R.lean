/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ListMatrix.getD_transpose
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/ListMatrix.lean, line 83
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Mathlib.Tactic.Matrix.ListMatrix
variable {α : Type*}

theorem getD_transpose [Zero α] {n j : Nat} (rows : List (List α)) (i : Nat) (hj : j < n) :
    ((transpose n rows).getD j []).getD i 0 = (rows.getD i []).getD j 0 := by
  have key : ∀ (r : List α) (cols : List (List α)) (j : Nat), j < cols.length →
      (consPad r cols).getD j [] = r.getD j 0 :: cols.getD j [] := by
    intro r
    induction r with
    | nil =>
      intro cols j hj
      first
      | (simp [consPad, List.getD_eq_getElem?_getD]; done)
      | (induction cols generalizing j with
         | nil => simp at hj
         | cons c cs ih =>
           cases j <;> simp_all [consPad, List.getD_eq_getElem?_getD])
    | cons a as ih =>
      intro cols j hj
      cases cols with
      | nil => simp at hj
      | cons c cs =>
        cases j with
        | zero => simp [consPad]
        | succ j =>
          have hj' : j < cs.length := by simpa using hj
          first
          | (simp [consPad, ih cs j hj']; done)
          | (simp_all [consPad, List.getD_eq_getElem?_getD])
  induction rows generalizing i with
  | nil => simp_all [transpose, List.getD_eq_getElem?_getD]
  | cons r rs ih =>
    have hlen : j < (transpose n rs).length := by
      first
      | simp [hj]
      | simpa using hj
    have e : transpose n (r :: rs) = consPad r (transpose n rs) := by
      first
      | rfl
      | simp [transpose]
    rw [e, key r _ j hlen]
    cases i with
    | zero => simp
    | succ i =>
      have h := ih i
      first
      | (simpa [List.getD_eq_getElem?_getD] using h)
      | (simp [List.getD_eq_getElem?_getD] at h ⊢; exact h)
      | (simp_all [List.getD_eq_getElem?_getD])
