/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_lt_top_iff
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 118
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma depth_lt_top_iff (N M : ModuleCat.{v} R) :
    N.depth M < ⊤ ↔ ∃ n, Nontrivial (Ext N M n) := by
  rw [lt_top_iff_ne_top, ne_eq, depth_eq_top_iff]
  constructor
  · intro h
    by_contra h'
    exact h fun i => not_nontrivial_iff_subsingleton.mp fun hi => h' ⟨i, hi⟩
  · rintro ⟨n, hn⟩ h
    exact not_nontrivial_iff_subsingleton.mpr (h n) hn
