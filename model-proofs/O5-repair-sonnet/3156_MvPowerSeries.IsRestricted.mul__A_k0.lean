/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MvPowerSeries.IsRestricted.mul
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/MvPowerSeries/Restricted.lean, line 131
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma mul [IsUltrametricDist R] {c : σ → ℝ} {f g : MvPowerSeries σ R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) : IsRestricted c (f * g) := by
  classical
  have hC : ∀ a b : σ →₀ ℕ, (a + b).prod (c · ^ ·) = a.prod (c · ^ ·) * b.prod (c · ^ ·) := by
    intro a b
    exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
  have := tendsto_antidiagonal (M := σ →₀ ℕ) (S := R)
    (C := fun t => t.prod (c · ^ ·)) hC
    (f := fun t => coeff t f) (g := fun t => coeff t g) hf hg
  unfold IsRestricted
  simp_rw [coeff_mul]
  exact this
