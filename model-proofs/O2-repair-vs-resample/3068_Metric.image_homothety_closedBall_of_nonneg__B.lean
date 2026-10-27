/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_closedBall_of_nonneg
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 159
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem Metric.image_homothety_closedBall_of_nonneg (p c : Q) {r : ℝ} (hr : 0 ≤ r) (x : 𝕜) :
    homothety c x '' closedBall p r = closedBall (homothety c x p) (‖x‖ * r) := by
  first
  | (rw [image_homothety, IsometryEquiv.image_closedBall, smul_closedBall _ _ hr,
      IsometryEquiv.image_closedBall]
     simp [homothety_apply])
  | (rcases eq_or_ne x 0 with rfl | hx
     · have hne : (closedBall p r).Nonempty := nonempty_closedBall.2 hr
       ext y
       simp only [Set.mem_image, homothety_zero, AffineMap.const_apply, norm_zero, zero_mul,
         closedBall_zero, Set.mem_singleton_iff]
       constructor
       · rintro ⟨z, -, rfl⟩
         rfl
       · rintro rfl
         exact ⟨p, mem_closedBall_self hr, rfl⟩
     · exact Metric.image_homothety_closedBall p c r hx)
