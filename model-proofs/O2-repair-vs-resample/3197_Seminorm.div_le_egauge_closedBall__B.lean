/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Seminorm.div_le_egauge_closedBall
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Convex/EGauge.lean, line 315
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma div_le_egauge_closedBall (r : ℝ≥0) (x : E) :
    (p x).toNNReal / r ≤ egauge 𝕜 (p.closedBall 0 r) x := by
  rw [le_egauge_iff]
  rintro c ⟨y, hy, rfl⟩
  rw [Seminorm.mem_closedBall_zero] at hy
  apply ENNReal.div_le_of_le_mul
  rw [map_smul_eq_mul]
  have : (‖c‖ * p y).toNNReal ≤ ‖c‖₊ * r := by
    rw [Real.toNNReal_le_iff_le_coe]
    push_cast
    exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)
  calc ((‖c‖ * p y).toNNReal : ℝ≥0∞) ≤ ((‖c‖₊ * r : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.2 this
    _ = ‖c‖ₑ * r := by rw [ENNReal.coe_mul, enorm_eq_nnnorm]
