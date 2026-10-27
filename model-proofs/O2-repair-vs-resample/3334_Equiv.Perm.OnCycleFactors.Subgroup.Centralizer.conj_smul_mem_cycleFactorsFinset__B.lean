/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Equiv.Perm.OnCycleFactors.Subgroup.Centralizer.conj_smul_mem_cycleFactorsFinset
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Perm/Centralizer.lean, line 116
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma Subgroup.Centralizer.conj_smul_mem_cycleFactorsFinset {k c : Perm α}
    (k_mem : k ∈ centralizer {g}) (c_mem : c ∈ g.cycleFactorsFinset) :
    MulAut.conj k • c ∈ g.cycleFactorsFinset := by
  have hk : k * g * k⁻¹ = g := by
    have := mem_centralizer_singleton_iff.mp k_mem
    first
    | rw [this, mul_assoc, mul_inv_cancel, mul_one]
    | rw [← this, mul_assoc, mul_inv_cancel, mul_one]
    | (rw [mul_inv_eq_iff_eq_mul]; exact this)
    | (rw [mul_inv_eq_iff_eq_mul]; exact this.symm)
  rw [MulAut.smul_def, MulAut.conj_apply]
  rw [← hk]
  first
  | exact (mem_cycleFactorsFinset_conj _ _ _).mpr c_mem
  | (rw [mem_cycleFactorsFinset_conj]; exact c_mem)
  | exact (mem_cycleFactorsFinset_conj' _ _ _).mpr c_mem
