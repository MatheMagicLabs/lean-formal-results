/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_sphere_of_nonneg
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 170
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  · obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    have ha : dist ((r / ‖w‖) • w +ᵥ p) p = r := by
      rw [dist_eq_norm_vsub, vadd_vsub, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hr (norm_nonneg w)),
        div_mul_cancel₀ _ hw']
    ext q
    simp [homothety_zero, Set.mem_image, eq_comm]
    exact fun _ => ⟨(r / ‖w‖) • w +ᵥ p, ha.symm⟩
  · exact image_homothety_sphere p c r hx
