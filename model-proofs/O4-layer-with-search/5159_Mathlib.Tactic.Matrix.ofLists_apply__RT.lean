/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ofLists_apply
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/OfLists.lean, line 64
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
  | zero => exact i.elim0
  | succ m ih =>
    cases rows with
    | nil =>
      refine Fin.cases ?_ (fun j => ?_) i
      · ext k
        simp [ofLists, ofListsFun, ofList_apply] at *
      · have := ih [] j
        ext k
        have hk := congrFun this k
        simp [ofLists, ofListsFun, ofList_apply] at *
        first
          | exact hk
          | simp_all
    | cons r rs =>
      refine Fin.cases ?_ (fun j => ?_) i
      · ext k
        simp [ofLists, ofListsFun, ofList_apply] at *
      · have := ih rs j
        ext k
        have hk := congrFun this k
        simp [ofLists, ofListsFun, ofList_apply] at *
        first
          | exact hk
          | simp_all
