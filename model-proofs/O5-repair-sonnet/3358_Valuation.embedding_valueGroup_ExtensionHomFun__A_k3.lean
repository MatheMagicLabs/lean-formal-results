/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.embedding_valueGroup₀ExtensionHomFun
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 373
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp]
private theorem embedding_valueGroup₀ExtensionHomFun (a : v.ValueGroup₀) :
    embedding (v.valueGroup₀ExtensionHomFun a) = embedding a := by
  unfold valueGroup₀ExtensionHomFun
  generalize hr : Function.surjInv (restrict₀_surjective (v : K →*₀ Γ₀)) a = r
  have h : restrict₀ (v : K →*₀ Γ₀) r = a := by
    rw [← hr]
    exact Function.surjInv_eq _ a
  subst h
  simp
