/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AddSubgroup.coe_zmultiplesEquivInt_symm_apply
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Group/Subgroup/ZPowers/Lemmas.lean, line 63
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-haiku, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-haiku-4-5
Setup:       Haiku 4.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp]
theorem coe_zmultiplesEquivInt_symm_apply (ha : a ≠ 0) (n : ℤ) :
    ((zmultiplesEquivInt ha).symm n : A) = n • a := by
  rfl
