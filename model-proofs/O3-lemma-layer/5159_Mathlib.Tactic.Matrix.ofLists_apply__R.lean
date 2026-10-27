/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ofLists_apply
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/OfLists.lean, line 64
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 3 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Matrix
namespace Mathlib.Tactic.Matrix
variable {α : Type*}

@[simp]
theorem ofLists_apply [Zero α] (m n : ℕ) (rows : List (List α)) (i : Fin m) :
    ofLists m n rows i = ofList n (rows.getD i []) := by
  funext j
  simp only [ofLists, ofList, Matrix.of_apply]
  induction m generalizing rows with
  | zero => exact i.elim0
  | succ m ih =>
    cases rows with
    | nil =>
      refine Fin.cases ?_ (fun k => ?_) i
      · first
        | (simp [ofListsFun])
        | (simp [ofListsFun, ofList])
        | rfl
      · have := ih [] k
        first
        | (simp_all [ofListsFun])
        | (simp [ofListsFun] at this ⊢; exact this)
        | (simp [ofListsFun]; simpa using this)
    | cons r rs =>
      refine Fin.cases ?_ (fun k => ?_) i
      · first
        | (simp [ofListsFun, ofList])
        | (simp [ofListsFun])
        | rfl
      · have := ih rs k
        first
        | (simp_all [ofListsFun])
        | (simp [ofListsFun] at this ⊢; exact this)
        | (simp [ofListsFun]; simpa using this)
