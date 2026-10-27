/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_sphere_of_nonneg
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 170
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  by_cases hx : x = 0
  · subst x
    obtain ⟨v, hv⟩ : (sphere (0 : W) r).Nonempty := by
      rwa [NormedSpace.sphere_nonempty]
    have hp : v +ᵥ p ∈ sphere p r := by
      rw [Metric.mem_sphere, dist_eq_norm_vsub W, vadd_vsub]
      simpa only [Metric.mem_sphere, dist_zero_right] using hv
    simp
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp [Function.const]
    · intro hy
      have hy' : y = c := Set.mem_singleton_iff.mp hy
      subst y
      exact ⟨v +ᵥ p, hp, rfl⟩
  · apply Metric.image_homothety_sphere
    exact hx
