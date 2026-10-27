/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.ae_enorm_bilin_le_of_ae_nnnorm_le
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean, line 260
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private lemma ae_enorm_bilin_le_of_ae_nnnorm_le {b : E → F → G} {c : ℝ≥0}
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ c * ‖f x‖₊ * ‖g x‖₊) :
    ∀ᵐ x ∂μ, ‖b (f x) (g x)‖ₑ ≤ c * ‖f x‖ₑ * ‖g x‖ₑ := by
  filter_upwards [h] with x hx
  simp only [enorm_eq_nnnorm]
  exact_mod_cast hx
