/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_closedBall_of_nonneg
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 159
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  LS1-leanstral-loop, arm L3, verified in round 3 (round 0 = first attempt)
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 in a fixed check-and-repair loop: L1 = 1 candidate per round, L3 = up to 3
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

theorem Metric.image_homothety_closedBall_of_nonneg (p c : Q) {r : ℝ} (hr : 0 ≤ r) (x : 𝕜) :
    homothety c x '' closedBall p r = closedBall (homothety c x p) (‖x‖ * r) := by
  by_cases hx : x = 0
  · subst hx
    have hne : (closedBall p r).Nonempty := ⟨p, Metric.mem_closedBall.mpr (by simpa [dist_self] using hr)⟩
    ext q
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact Metric.mem_closedBall.mpr (by simpa [dist_self])
    · intro hq
      have hq' : q = c := by
        simpa [Metric.mem_closedBall, dist_self] using hq
      rcases hne with ⟨a, ha⟩
      refine ⟨a, ha, ?_⟩
      simp [hq', homothety_apply]
  · exact Metric.image_homothety_closedBall p c r hx
