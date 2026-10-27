/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_closedBall
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 153
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm Z, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

noncomputable section
open NNReal
variable {V P W Q : Type*} [SeminormedAddCommGroup V] [PseudoMetricSpace P] [NormedAddTorsor V P]
section NormedSpace
variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W]
open AffineMap
open scoped Pointwise in

theorem Metric.image_homothety_closedBall (p c : P) (r : ℝ) {x : 𝕜} (hx : x ≠ 0) :
    homothety c x '' closedBall p r = closedBall (homothety c x p) (‖x‖ * r) := by
  have hd (a b : P) :
      dist (homothety c x a) (homothety c x b) = ‖x‖ * dist a b := by
    simp [homothety_def, dist_eq_norm_vsub V, ← smul_sub, norm_smul]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Metric.mem_closedBall] at hz ⊢
    rw [hd]
    exact mul_le_mul_of_nonneg_left hz (norm_nonneg x)
  · intro hy
    let z : P := homothety c x⁻¹ y
    have hz : homothety c x z = y := by
      simp [z, homothety_def, smul_smul, hx]
    refine ⟨z, ?_, hz⟩
    rw [Metric.mem_closedBall] at hy ⊢
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hle : ‖x‖ * dist z p ≤ ‖x‖ * r := by
      calc
        ‖x‖ * dist z p =
            dist (homothety c x z) (homothety c x p) := (hd z p).symm
        _ = dist y (homothety c x p) := by rw [hz]
        _ ≤ ‖x‖ * r := hy
    nlinarith
