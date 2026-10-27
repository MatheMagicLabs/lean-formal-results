/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Seminorm.div_le_egauge_closedBall
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Convex/EGauge.lean, line 315
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
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
  rw [enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe, Real.toNNReal_le_iff_le_coe,
    map_smul_eq_mul]
  push_cast
  gcongr
