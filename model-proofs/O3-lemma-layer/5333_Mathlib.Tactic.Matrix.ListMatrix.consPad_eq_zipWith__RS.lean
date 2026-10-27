/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ListMatrix.consPad_eq_zipWith
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/ListMatrix.lean, line 64
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Mathlib.Tactic.Matrix.ListMatrix
variable {α : Type*}

theorem consPad_eq_zipWith [Zero α] (row : List α) (cols : List (List α)) :
    consPad row cols = List.zipWith List.cons (row.rightpad cols.length 0) cols := by
  induction cols generalizing row with
  | nil => cases row <;> simp [consPad]
  | cons c cs ih =>
    cases row with
    | nil => simp [consPad, ih, List.rightpad, List.replicate_succ]
    | cons a as => simp [consPad, ih, List.rightpad]
