/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Seminorm.induction_sup_of_continuous
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/LocallyConvex/WithSeminorms.lean, line 1035
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma induction_sup_of_continuous [TopologicalSpace E] (hp : WithSeminorms p)
    {motive : Seminorm 𝕜 E → Prop}
    (base : ∀ i, motive (p i))
    (zero : motive 0)
    (sup : ∀ r s, motive r → motive s → motive (r ⊔ s))
    (le : ∀ r s, r ≤ s → motive s → motive r)
    (smul : ∀ r (C : ℝ≥0), motive r → motive (C • r))
    {q : Seminorm 𝕜 E} (cont : Continuous q) :
    motive q := by
  obtain ⟨s, C, -, hC⟩ := bound_of_continuous hp q cont
  refine le q _ hC (smul _ C ?_)
  clear hC
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, Seminorm.bot_eq_zero]
    exact zero
  | insert a s _ hs =>
    rw [Finset.sup_insert]
    exact sup _ _ (base a) hs
