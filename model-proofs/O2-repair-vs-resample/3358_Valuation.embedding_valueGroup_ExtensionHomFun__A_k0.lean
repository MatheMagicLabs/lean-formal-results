/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.embedding_valueGroup₀ExtensionHomFun
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 373
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp]
private theorem embedding_valueGroup₀ExtensionHomFun (a : v.ValueGroup₀) :
    embedding (v.valueGroup₀ExtensionHomFun a) = embedding a := by
  have h := Function.surjInv_eq (restrict₀_surjective (v : K →*₀ Γ₀)) a
  conv_rhs => rw [← h]
  simp only [valueGroup₀ExtensionHomFun]
  simp
