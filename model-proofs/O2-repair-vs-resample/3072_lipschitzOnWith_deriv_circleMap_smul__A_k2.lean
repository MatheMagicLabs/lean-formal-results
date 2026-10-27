/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     lipschitzOnWith_deriv_circleMap_smul
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 47
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private theorem lipschitzOnWith_deriv_circleMap_smul {α : Type*} [PseudoEMetricSpace α]
    {t : Set α} {g : α → E} {θ b : ℝ} (hg : LipschitzOnWith ‖b‖₊ g t) :
    LipschitzOnWith ‖|R| * b‖₊ (fun x ↦ deriv (circleMap c R) θ • g x) t := by
  intro x hx y hy
  have h1 := hg hx hy
  have h : ‖deriv (circleMap c R) θ‖₊ = ‖|R|‖₊ := by
    apply NNReal.eq
    simp [deriv_circleMap]
  simp only [edist_nndist, nndist_eq_nnnorm] at h1 ⊢
  rw [← smul_sub, nnnorm_smul, h, nnnorm_mul, ENNReal.coe_mul, ENNReal.coe_mul, mul_assoc]
  gcongr
