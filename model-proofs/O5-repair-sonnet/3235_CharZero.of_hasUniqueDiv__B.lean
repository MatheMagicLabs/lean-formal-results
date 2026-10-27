/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CharZero.of_hasUniqueDiv
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Module/Torsion/Free.lean, line 217
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma CharZero.of_hasUniqueDiv [Nontrivial M] [HasUniqueDiv M] : CharZero R := by
  have key : ∀ a b : ℕ, a < b → (a : R) = (b : R) → False := by
    intro a b hlt h
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have h1 : a • x = (a + k + 1) • x :=
      (Nat.cast_smul_eq_nsmul R a x).symm.trans
        ((congrArg (fun r : R => r • x) h).trans (Nat.cast_smul_eq_nsmul R _ x))
    have h2 : (k + 1) • x = 0 := by
      have h3 : a • x + (k + 1) • x = a • x + 0 := by
        rw [add_zero, ← add_nsmul, ← Nat.add_assoc]
        exact h1.symm
      exact add_left_cancel h3
    have hinj : Function.Injective (fun y : M => (k + 1) • y) :=
      nsmul_right_injective (Nat.succ_ne_zero k)
    apply hx
    apply hinj
    show (k + 1) • x = (k + 1) • (0 : M)
    rw [smul_zero]
    exact h2
  refine ⟨fun m n h => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h' | h'
  · exact key m n h' h
  · exact key n m h' h.symm
