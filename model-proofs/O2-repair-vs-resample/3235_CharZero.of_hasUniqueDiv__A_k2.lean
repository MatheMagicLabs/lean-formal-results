/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CharZero.of_hasUniqueDiv
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Module/Torsion/Free.lean, line 217
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma CharZero.of_hasUniqueDiv [Nontrivial M] [HasUniqueDiv M] : CharZero R := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  refine ⟨fun n m hnm => ?_⟩
  have h : n • x = m • x := by
    rw [← Nat.cast_smul_eq_nsmul R n x, hnm, Nat.cast_smul_eq_nsmul]
  by_contra hne
  have h2 : ((n : ℤ) - m) • x = 0 := by
    rw [sub_smul]; simp [h]
  have hz : ((n : ℤ) - m) ≠ 0 := by omega
  apply hx
  exact zsmul_right_injective hz (by simp [h2])
