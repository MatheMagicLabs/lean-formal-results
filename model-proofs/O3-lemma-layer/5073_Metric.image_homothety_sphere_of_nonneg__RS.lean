/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_sphere_of_nonneg
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 170
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

theorem Metric.image_homothety_sphere_of_nonneg [NormedSpace ℝ W] [Nontrivial W]
    (p c : Q) {r : ℝ} (hr : 0 ≤ r) (x : 𝕜) :
    homothety c x '' sphere p r = sphere (homothety c x p) (‖x‖ * r) := by
  rcases eq_or_ne x 0 with rfl | hx
  · obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0:W)) (r := r)).mpr hr
    have hne : (Metric.sphere p r).Nonempty :=
      ⟨v +ᵥ p, by rw [Metric.mem_sphere, dist_vadd_left]; simpa using hv⟩
    simp only [norm_zero, zero_mul, Metric.sphere_zero]
    have this : ((homothety c (0:𝕜) : Q →ᵃ[𝕜] Q) : Q → Q) = fun _ => c := by
      funext y; simp [homothety_apply]
    rw [this, hne.image_const]
  · exact Metric.image_homothety_sphere p c r hx
