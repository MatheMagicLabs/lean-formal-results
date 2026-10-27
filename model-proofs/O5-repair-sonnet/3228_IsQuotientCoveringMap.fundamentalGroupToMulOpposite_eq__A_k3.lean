/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsQuotientCoveringMap.fundamentalGroupToMulOpposite_eq
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Homotopy/Lifting.lean, line 683
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem fundamentalGroupToMulOpposite_eq [IsMulCommutative G] (e' : p ⁻¹' {x}) :
    hp.fundamentalGroupToMulOpposite e = hp.fundamentalGroupToMulOpposite e' := by
  obtain ⟨g, rfl⟩ := hp.exists_toPermFiber_eq e e'
  have hc : ∀ a : G, g * a * g⁻¹ = a := fun a => by
    have h : g * a = a * g := by
      first
        | exact mul_comm g a
        | exact Std.Commutative.comm g a
        | exact IsMulCommutative.is_comm.comm g a
    rw [h, mul_inv_cancel_right]
  ext γ
  rw [hp.fundamentalGroupToMulOpposite_toPermFiber]
  simp only [hc, MulOpposite.op_unop]
