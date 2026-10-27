/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CharZero.of_hasUniqueDiv
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Module/Torsion/Free.lean, line 217
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma CharZero.of_hasUniqueDiv [Nontrivial M] [HasUniqueDiv M] : CharZero R := by
  constructor
  intro a b hab
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have this : a • x = b • x := by
    rw [← Nat.cast_smul_eq_nsmul R a x, ← Nat.cast_smul_eq_nsmul R b x, hab]
  by_contra h
  have hne : (a : ℤ) - b ≠ 0 := by omega
  apply hx
  apply zsmul_right_injective hne
  first
    | simp only [smul_zero, sub_smul, natCast_zsmul, this, sub_self]
    | simp [sub_smul, this]
