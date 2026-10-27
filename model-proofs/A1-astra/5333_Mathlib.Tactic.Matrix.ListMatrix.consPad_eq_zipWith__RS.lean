/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ListMatrix.consPad_eq_zipWith
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/ListMatrix.lean, line 64
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Mathlib.Tactic.Matrix.ListMatrix
variable {α : Type*}

theorem consPad_eq_zipWith [Zero α] (row : List α) (cols : List (List α)) :
    consPad row cols = List.zipWith List.cons (row.rightpad cols.length 0) cols := by
  induction cols generalizing row with
  | nil =>
      cases row <;> simp [consPad]
  | cons col cols ih =>
      cases row with
      | nil =>
          simpa [consPad, List.rightpad, List.replicate_succ] using
            congrArg (List.cons (0 :: col)) (ih [])
      | cons a row =>
          simpa [consPad, List.rightpad] using
            congrArg (List.cons (a :: col)) (ih row)
