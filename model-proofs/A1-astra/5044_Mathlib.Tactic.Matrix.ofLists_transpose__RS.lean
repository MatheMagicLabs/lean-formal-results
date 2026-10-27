/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ofLists_transpose
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/OfLists.lean, line 78
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Matrix
namespace Mathlib.Tactic.Matrix
variable {α : Type*}

@[simp]
theorem ofLists_transpose [Zero α] (m n : ℕ) (rows : List (List α)) :
    ofLists n m (ListMatrix.transpose n rows) = (ofLists m n rows)ᵀ := by
  ext i j
  simp only [Matrix.transpose_apply, ofLists_apply, ofList_apply]
  exact ListMatrix.getD_transpose rows (j : ℕ) i.isLt
