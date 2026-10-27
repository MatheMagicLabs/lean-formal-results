/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ListMatrix.getD_transpose
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/ListMatrix.lean, line 83
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Mathlib.Tactic.Matrix.ListMatrix
variable {α : Type*}

theorem getD_transpose [Zero α] {n j : Nat} (rows : List (List α)) (i : Nat) (hj : j < n) :
    ((transpose n rows).getD j []).getD i 0 = (rows.getD i []).getD j 0 := by
  have hlen (xs : List α) (ys : List (List α)) :
      (consPad xs ys).length = ys.length := by
    induction ys generalizing xs with
    | nil => cases xs <;> simp [consPad]
    | cons y ys ih => cases xs <;> simp_all [consPad]
  have hget (xs : List α) (ys : List (List α)) (k : Nat)
      (hk : k < ys.length) :
      (consPad xs ys).getD k [] =
        xs.getD k 0 :: ys.getD k [] := by
    induction ys generalizing xs k with
    | nil => simp at hk
    | cons y ys ih =>
      cases xs <;> cases k <;>
        simp_all [consPad, List.getD]
  have htlen (rs : List (List α)) :
      (transpose n rs).length = n := by
    induction rs with
    | nil => simp [transpose]
    | cons r rs ih => simpa [transpose, hlen] using ih
  induction rows generalizing i with
  | nil =>
    simp [transpose, List.getD, hj]
  | cons r rs ih =>
    rw [transpose, hget r (transpose n rs) j (by simpa [htlen] using hj)]
    cases i with
    | zero => simp [List.getD]
    | succ i => simpa [List.getD] using ih i
