/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_top_iff
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 96
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma depth_eq_top_iff (N M : ModuleCat.{v} R) :
    N.depth M = ⊤ ↔ ∀ i, Subsingleton (Ext N M i) := by
  constructor
  · intro h i
    by_contra hi
    rw [not_subsingleton_iff_nontrivial] at hi
    have := depth_eq_find N M ⟨i, hi⟩
    rw [h] at this
    first
      | exact (ENat.coe_ne_top _) this.symm
      | exact (ENat.top_ne_coe _) this
      | simp at this
  · intro h
    unfold depth
    refine eq_top_iff.mpr (le_sSup ?_)
    exact fun i _ => h i
