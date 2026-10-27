/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MvPowerSeries.IsRestricted.smul
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/MvPowerSeries/Restricted.lean, line 123
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma smul {c : σ → ℝ} (r : R) {f : MvPowerSeries σ R} (hf : IsRestricted c f) :
    IsRestricted c (r • f) := by
  have h := isRestricted_map c (fun x => r * x) (C := ‖r‖) (fun x => norm_mul_le r x) hf
  first
    | exact h
    | (convert h using 1
       ext t
       first
         | rfl
         | simp [coeff_apply]
         | simp)
