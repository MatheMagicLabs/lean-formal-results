/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MvPowerSeries.IsRestricted.mul
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/MvPowerSeries/Restricted.lean, line 131
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma mul [IsUltrametricDist R] {c : σ → ℝ} {f g : MvPowerSeries σ R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) : IsRestricted c (f * g) := by
  classical
  unfold IsRestricted at *
  simp_rw [coeff_mul]
  exact tendsto_antidiagonal (C := fun t => t.prod (c · ^ ·))
    (f := fun t => coeff t f) (g := fun t => coeff t g)
    (fun a b => Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _))
    hf hg
