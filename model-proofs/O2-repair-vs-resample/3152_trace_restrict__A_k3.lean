/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     trace_restrict
Source:      Mathlib @ a02a63c2, Mathlib/NumberTheory/ModularForms/NormTrace.lean, line 291
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma trace_restrict (hGH : 𝒢 ≤ ℋ) :
    .trace ℋ (f.restrict hGH) = 𝒢.relIndex ℋ • f := by
  ext τ
  have key : ∀ n : ℕ, (n • f) τ = n • f τ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [succ_nsmul, succ_nsmul, ModularForm.add_apply, ih]
  rw [key]
  simp [ModularForm.coe_trace, quotientFunc_restrict, Finset.sum_apply, Finset.sum_const,
    Finset.card_univ, Fintype.card_eq_nat_card, Subgroup.relIndex, Subgroup.index]
