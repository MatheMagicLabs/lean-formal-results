/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ofLists_apply
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/OfLists.lean, line 64
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Matrix
namespace Mathlib.Tactic.Matrix
variable {α : Type*}

@[simp]
theorem ofLists_apply [Zero α] (m n : ℕ) (rows : List (List α)) (i : Fin m) :
    ofLists m n rows i = ofList n (rows.getD i []) := by
  induction m generalizing rows with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · cases rows <;> ext j <;>
        simp [ofLists, ofListsFun, ofList_apply]
    · cases rows with
      | nil =>
        ext j
        simpa [ofLists, ofListsFun, ofList_apply] using
          congrFun (ih [] i) j
      | cons row rows =>
        ext j
        simpa [ofLists, ofListsFun, ofList_apply] using
          congrFun (ih rows i) j
