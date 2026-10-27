/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsQuotientCoveringMap.fundamentalGroupToMulOpposite_eq
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Homotopy/Lifting.lean, line 683
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem fundamentalGroupToMulOpposite_eq [IsMulCommutative G] (e' : p ⁻¹' {x}) :
    hp.fundamentalGroupToMulOpposite e = hp.fundamentalGroupToMulOpposite e' := by
  obtain ⟨g, rfl⟩ := hp.exists_toPermFiber_eq e e'
  have hc : ∀ a b : G, a * b = b * a := IsMulCommutative.is_comm.comm
  refine MonoidHom.ext fun γ ↦ ?_
  rw [hp.fundamentalGroupToMulOpposite_toPermFiber, hc g, mul_inv_cancel_right,
    MulOpposite.op_unop]
