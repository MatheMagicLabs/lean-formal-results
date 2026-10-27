/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Function.locallyFinsuppWithin.truncate_truncate
Source:      Mathlib @ a02a63c2, Mathlib/Topology/LocallyFinsupp.lean, line 862
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp] lemma truncate_truncate (D : locallyFinsuppWithin U Y) (y₁ y₂ : Y) (hy₁ : 0 ≤ y₁)
    (hy₂ : 0 ≤ y₂) :
    (D.truncate y₁ hy₁).truncate y₂ hy₂ = D.truncate (min y₁ y₂) (le_min hy₁ hy₂) := by
  ext z
  first
  | (simp only [truncate_apply, min_assoc]; done)
  | (rw [truncate_apply, truncate_apply, truncate_apply, min_assoc]; done)
  | (simp [min_assoc]; done)
