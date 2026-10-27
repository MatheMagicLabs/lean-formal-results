/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     hasDerivAt_circleAverage_herglotzRieszKernel_smul
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/Poisson.lean, line 302
             (added after the model's training data; human proof 30 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 4 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem hasDerivAt_circleAverage_herglotzRieszKernel_smul (hg : CircleIntegrable f 0 R)
    (hw : w ∉ sphere 0 |R|) :
    HasDerivAt (fun w ↦ circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • f ζ) 0 R)
      (circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • f ζ) 0 R) w := by
  let d : ℝ := |(|R| - ‖w‖)|
  have hd : 0 < d := by simpa [d, abs_pos, sub_ne_zero, mem_sphere, dist_eq_norm, eq_comm] using hw
  have hd₂ : 0 < d / 2 := half_pos hd
  have hdist (z : ℂ) (hz : ‖z‖ = |R|) (x : ℂ) (hx : x ∈ ball w (d / 2)) : d / 2 ≤ ‖z - x‖ := by {
  have h₁ : d ≤ ‖z - w‖ := by { simpa [d, hz] using abs_norm_sub_norm_le z w }
  have h₂ : ‖x - w‖ < d / 2 := mem_ball_iff_norm.mp hx
  have h₃ : ‖z - w‖ ≤ ‖z - x‖ + ‖x - w‖ := by { simpa only [sub_add_sub_cancel] using norm_add_le (z - x) (x - w) }
  linarith }
  have hne (z : ℂ) (hz : ‖z‖ = |R|) (x : ℂ) (hx : x ∈ ball w (d / 2)) : z - x ≠ 0 := norm_pos_iff.mp (hd₂.trans_le (hdist z hz x hx))
  have hwball : w ∈ ball w (d / 2) := mem_ball_self hd₂
  have hoff (x : ℂ) (hx : x ∈ ball w (d / 2)) : x ∉ sphere 0 |R| := by { intro hz; exact hne x (by simpa [mem_sphere, dist_eq_norm] using hz) x hx (sub_self x) }
  have hI (x : ℂ) (hx : x ∈ ball w (d / 2)) : CircleIntegrable (fun z ↦ herglotzRieszKernel 0 x z • f z) 0 R := hg.continuousOn_smul (continuousOn_herglotzRieszKernel_sphere (hoff x hx))
  have hJ : CircleIntegrable (fun z ↦ (2 * z / (z - w) ^ 2) • f z) 0 R := by { apply hg.continuousOn_smul; apply ContinuousOn.div (by fun_prop) (by fun_prop); intro z hz; exact pow_ne_zero 2 (hne z (by simpa [mem_sphere, dist_eq_norm] using hz) w hwball) }
  have hz (θ : ℝ) : ‖circleMap 0 R θ‖ = |R| := by simp [circleMap, Complex.norm_mul]
  have hk (θ : ℝ) (x : ℂ) (hx : x ∈ ball w (d / 2)) : HasDerivAt (fun x ↦ herglotzRieszKernel 0 x (circleMap 0 R θ)) (2 * circleMap 0 R θ / (circleMap 0 R θ - x) ^ 2) x := by { simp only [herglotzRieszKernel, sub_zero]; convert ((hasDerivAt_const x (circleMap 0 R θ)).add (hasDerivAt_id x)).div ((hasDerivAt_const x (circleMap 0 R θ)).sub (hasDerivAt_id x)) (hne _ (hz θ) x hx) using 1 <;> first | rfl | (simp only [Pi.sub_apply, Pi.add_apply, id_eq]; ring) }
  have hder (θ : ℝ) (x : ℂ) (hx : x ∈ ball w (d / 2)) : HasDerivAt (fun x ↦ herglotzRieszKernel 0 x (circleMap 0 R θ) • f (circleMap 0 R θ)) ((2 * circleMap 0 R θ / (circleMap 0 R θ - x) ^ 2) • f (circleMap 0 R θ)) x := (hk θ x hx).smul_const _
  have hbound (θ : ℝ) (x : ℂ) (hx : x ∈ ball w (d / 2)) : ‖(2 * circleMap 0 R θ / (circleMap 0 R θ - x) ^ 2) • f (circleMap 0 R θ)‖ ≤ (2 * |R| / (d / 2) ^ 2) * ‖f (circleMap 0 R θ)‖ := by { rw [norm_smul, norm_div, norm_mul, norm_pow, hz]; norm_num only [Complex.norm_ofNat]; gcongr; exact hdist _ (hz θ) x hx }
  have hg' : IntervalIntegrable (fun θ ↦ f (circleMap 0 R θ)) volume 0 (2 * π) := hg
  have hi : HasDerivAt (fun x ↦ ∫ θ in 0..2 * π, herglotzRieszKernel 0 x (circleMap 0 R θ) • f (circleMap 0 R θ)) (∫ θ in 0..2 * π, (2 * circleMap 0 R θ / (circleMap 0 R θ - w) ^ 2) • f (circleMap 0 R θ)) w := by {
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (F' := fun x θ ↦ (2 * circleMap 0 R θ / (circleMap 0 R θ - x) ^ 2) • f (circleMap 0 R θ)) (s := ball w (d / 2)) (bound := fun θ ↦ (2 * |R| / (d / 2) ^ 2) * ‖f (circleMap 0 R θ)‖) ?_ ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact ball_mem_nhds w hd₂
  · filter_upwards [ball_mem_nhds w hd₂] with x hx using (intervalIntegrable_iff.mp (hI x hx)).aestronglyMeasurable
  · exact hI w hwball
  · exact (intervalIntegrable_iff.mp hJ).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun θ _ x hx ↦ hbound θ x hx)
  · exact hg'.norm.const_mul _
  · exact Filter.Eventually.of_forall (fun θ _ x hx ↦ hder θ x hx) }
  simpa only [circleAverage, Pi.smul_def] using hi.const_smul ((2 * π)⁻¹ : ℝ)
