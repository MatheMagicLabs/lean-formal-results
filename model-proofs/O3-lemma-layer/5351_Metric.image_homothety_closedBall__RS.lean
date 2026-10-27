/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_closedBall
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 153
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  first
  | (rw [image_homothety, (IsometryEquiv.vaddConst c).symm.image_closedBall,
      smul_closedBall' hx, IsometryEquiv.image_closedBall]
     first
     | rfl
     | (congr 1; simp [AffineMap.homothety_apply]))
  | (rw [image_homothety, (IsometryEquiv.vaddConst c).symm.image_closedBall,
      ← Set.image_smul, Metric.smul_image_closedBall hx, IsometryEquiv.image_closedBall]
     first
     | rfl
     | (congr 1; simp [AffineMap.homothety_apply]))
  | (rw [image_homothety, (IsometryEquiv.vaddConst c).symm.image_closedBall,
      Metric.smul_image_closedBall hx, IsometryEquiv.image_closedBall]
     first
     | rfl
     | (congr 1; simp [AffineMap.homothety_apply]))
