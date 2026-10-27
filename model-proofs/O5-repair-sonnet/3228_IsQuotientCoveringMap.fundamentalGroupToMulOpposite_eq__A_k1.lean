/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsQuotientCoveringMap.fundamentalGroupToMulOpposite_eq
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Homotopy/Lifting.lean, line 683
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem fundamentalGroupToMulOpposite_eq [IsMulCommutative G] (e' : p ⁻¹' {x}) :
    hp.fundamentalGroupToMulOpposite e = hp.fundamentalGroupToMulOpposite e' := by
  obtain ⟨g, rfl⟩ := hp.exists_toPermFiber_eq e e'
  have key : ∀ a b : G, a * b = b * a := by
    intro a b
    first
      | exact mul_comm a b
      | exact IsMulCommutative.is_comm.comm a b
      | exact (IsMulCommutative.is_comm (M := G)).comm a b
      | exact Std.Commutative.comm a b
  refine MonoidHom.ext fun γ => ?_
  rw [hp.fundamentalGroupToMulOpposite_toPermFiber, key g, mul_assoc, mul_inv_cancel, mul_one,
    MulOpposite.op_unop]
