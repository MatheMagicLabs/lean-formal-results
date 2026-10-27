/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MvPowerSeries.isRestricted_map
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/MvPowerSeries/Restricted.lean, line 98
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma isRestricted_map {S : Type*} [NormedRing S] (c : σ → ℝ) (π : R → S) {C : ℝ}
    (hCπ : ∀ x, ‖π x‖ ≤ C * ‖x‖) {f : MvPowerSeries σ R} (hf : IsRestricted c f) :
    IsRestricted c (fun t ↦ π (coeff t f) : MvPowerSeries σ S) := by
  have hf' := (isRestricted_abs_iff c f).mpr hf
  refine (isRestricted_abs_iff c _).mp ?_
  have hP : ∀ t : σ →₀ ℕ, 0 ≤ t.prod (fun i n => |c| i ^ n) := fun t =>
    Finset.prod_nonneg fun i _ => pow_nonneg (abs_nonneg _) _
  have h2 : Tendsto (fun t : σ →₀ ℕ => C * (‖coeff t f‖ * t.prod (fun i n => |c| i ^ n)))
      cofinite (𝓝 0) := by
    have := Filter.Tendsto.const_mul C hf'
    rwa [mul_zero] at this
  refine squeeze_zero (fun t => mul_nonneg (norm_nonneg _) (hP t)) (fun t => ?_) h2
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hCπ _) (hP t)
