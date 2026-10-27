/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     aestronglyMeasurable_deriv_circleMap_smul
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 40
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private theorem aestronglyMeasurable_deriv_circleMap_smul {f : ℂ → E}
    (hf : AEStronglyMeasurable (f <| circleMap c R ·) (volume.restrict (Ι 0 (2 * π)))) :
    AEStronglyMeasurable (fun θ : ℝ ↦ deriv (circleMap c R) θ • f (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))) := by
  have h : deriv (circleMap c R) = fun θ => circleMap 0 R θ * Complex.I :=
    funext fun θ => deriv_circleMap c R θ
  rw [h]
  exact ((continuous_circleMap 0 R).mul continuous_const).aestronglyMeasurable.smul hf
