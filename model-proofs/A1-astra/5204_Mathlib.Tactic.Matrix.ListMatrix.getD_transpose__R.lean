/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ListMatrix.getD_transpose
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/ListMatrix.lean, line 83
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Mathlib.Tactic.Matrix.ListMatrix
variable {α : Type*}

theorem getD_transpose [Zero α] {n j : Nat} (rows : List (List α)) (i : Nat) (hj : j < n) :
    ((transpose n rows).getD j []).getD i 0 = (rows.getD i []).getD j 0 := by
  have hcons (r : List α) (cs : List (List α)) (k : Nat)
      (hk : k < cs.length) :
      (consPad r cs).getD k [] = r.getD k 0 :: cs.getD k [] := by
    induction cs generalizing r k with
    | nil => simp at hk
    | cons c cs ih =>
      cases r <;> cases k <;>
        simp_all [consPad, List.getD]
  induction rows generalizing i with
  | nil =>
    simp [transpose, List.getD, hj]
  | cons r rows ih =>
    change ((consPad r (transpose n rows)).getD j []).getD i 0 =
      ((r :: rows).getD i []).getD j 0
    rw [hcons r (transpose n rows) j (by simpa using hj)]
    cases i <;> simp_all [List.getD]
