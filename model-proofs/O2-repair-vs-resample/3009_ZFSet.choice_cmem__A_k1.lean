/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFSet.choice_cmem
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 534
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem choice_cmem (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y ∈ x) : choice x ′ y ᶜ∈ y := by
  have h1 : ((choice x : ZFClass.{u}) ′ (y : ZFClass.{u})) =
      ((Classical.epsilon fun z : ZFSet.{u} => z ∈ y : ZFSet.{u}) : ZFClass.{u}) := by
    letI : Definable₁ (fun y : ZFSet.{u} => Classical.epsilon fun z : ZFSet.{u} => z ∈ y) :=
      Classical.allZFSetDefinable _
    exact map_fval yx
  rw [h1]
  exact ZFClass.coe_cmem.2 (choice_mem_aux x h y yx)
