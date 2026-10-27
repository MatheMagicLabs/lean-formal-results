/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_sphere_of_nonneg
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 170
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  · obtain ⟨v, hv⟩ :=
      (NormedSpace.sphere_nonempty (E := W) (x := 0)).mpr hr
    have hs : (sphere p r).Nonempty := by
      refine ⟨v +ᵥ p, ?_⟩
      simpa [mem_sphere, dist_eq_norm_vsub] using hv
    subst x
    simp [homothety_apply, hs]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact Set.mem_singleton c
    · intro hy
      have hyc : y = c := Set.mem_singleton_iff.mp hy
      obtain ⟨z, hz⟩ := hs
      exact ⟨z, hz, hyc.symm⟩
  · apply Metric.image_homothety_sphere
    exact hx
