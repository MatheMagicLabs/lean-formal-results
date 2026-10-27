/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AddSubgroup.normalCore_eq_ker
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/GroupAction/Quotient.lean, line 434
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem _root_.AddSubgroup.normalCore_eq_ker {G : Type*} [AddGroup G] (H : AddSubgroup G) :
    H.normalCore = (AddAction.toPermHom G (G ⧸ H)).ker := by
  ext g
  rw [AddMonoidHom.mem_ker, AddAction.toPermHom_apply, ofMul_eq_zero, Equiv.Perm.ext_iff,
    QuotientAddGroup.forall_mk]
  apply Equiv.neg G |>.forall_congr
  simp [QuotientAddGroup.eq, eq_comm, add_assoc]
