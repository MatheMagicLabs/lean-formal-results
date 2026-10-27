/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     lipschitzOnWith_deriv_circleMap_smul
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean, line 47
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private theorem lipschitzOnWith_deriv_circleMap_smul {α : Type*} [PseudoEMetricSpace α]
    {t : Set α} {g : α → E} {θ b : ℝ} (hg : LipschitzOnWith ‖b‖₊ g t) :
    LipschitzOnWith ‖|R| * b‖₊ (fun x ↦ deriv (circleMap c R) θ • g x) t := by
  intro x hx y hy
  have h := hg hx hy
  have hd : ‖deriv (circleMap c R) θ‖₊ = ‖R‖₊ := by
    apply NNReal.eq
    simp [deriv_circleMap, norm_mul]
  have hb : ‖|R| * b‖₊ = ‖R‖₊ * ‖b‖₊ := by
    simp [nnnorm_mul]
  rw [edist_smul₀, ENNReal.smul_def, smul_eq_mul, hd, hb]
  calc (‖R‖₊ : ENNReal) * edist (g x) (g y)
      ≤ (‖R‖₊ : ENNReal) * ((‖b‖₊ : ENNReal) * edist x y) := by gcongr
    _ = ((‖R‖₊ * ‖b‖₊ : NNReal) : ENNReal) * edist x y := by
      rw [ENNReal.coe_mul]; ring
