/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CharZero.of_hasUniqueDiv
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Module/Torsion/Free.lean, line 217
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma CharZero.of_hasUniqueDiv [Nontrivial M] [HasUniqueDiv M] : CharZero R := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have key : ∀ m n : ℕ, (m : R) = n → m ≤ n → m = n := by
    intro m n h hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have h1 : m • x = (m + k) • x := by
      have := congrArg (fun r : R => r • x) h
      simpa only [Nat.cast_smul_eq_nsmul] using this
    rw [add_smul] at h1
    have h2 : k • x = 0 := by
      have : m • x + k • x = m • x + 0 := by rw [add_zero]; exact h1.symm
      exact add_left_cancel this
    by_contra hk
    have hk0 : k ≠ 0 := by omega
    exact hx ((nsmul_right_injective hk0 : Function.Injective (fun y : M => k • y))
      (show k • x = k • (0:M) by rw [smul_zero]; exact h2))
  refine ⟨fun m n h => ?_⟩
  rcases le_total m n with hmn | hmn
  · exact key m n h hmn
  · exact (key n m h.symm hmn).symm
