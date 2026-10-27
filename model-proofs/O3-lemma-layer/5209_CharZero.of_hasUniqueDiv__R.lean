/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CharZero.of_hasUniqueDiv
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Module/Torsion/Free.lean, line 217
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Module
variable {R S M N : Type*}
section Semiring
variable [Semiring R] [Semiring S]
section AddCommMonoid
variable [AddCommMonoid M] [Module R M] [Module S M] [AddCommMonoid N] [Module R N]
variable (R M) in
variable [IsTorsionFree R M]
variable (M) in
variable (R) in
variable [IsCancelMulZero R]
variable (M) in
variable [CharZero R]
variable (R M) in
end AddCommMonoid
section AddCommGroup
variable [CharZero R] [IsDomain R] [AddCommGroup M] [Module R M]
end AddCommGroup
end Semiring
section NonAssocSemiring
variable [NonAssocSemiring R] {n : ℕ}
end NonAssocSemiring
section Ring
variable [Ring R] [AddCommGroup M] [Module R M] {m : M} {r₁ r₂ : R}
variable [IsCancelMulZero R] [IsTorsionFree R M]
variable (R) in
end Ring
section Semiring
variable (R M) [Semiring R] [AddCommGroup M] [Module R M]

lemma CharZero.of_hasUniqueDiv [Nontrivial M] [HasUniqueDiv M] : CharZero R := by
  constructor
  intro a b hab
  by_contra h
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have key : a • x = b • x := by
    rw [← Nat.cast_smul_eq_nsmul R, hab, Nat.cast_smul_eq_nsmul]
  rcases Nat.lt_or_gt_of_ne h with hlt | hlt
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    rw [add_assoc, add_nsmul] at key
    have h0 : (k + 1) • x = (k + 1) • (0 : M) := by
      rw [smul_zero]
      apply add_left_cancel (a := a • x)
      rw [add_zero]
      exact key.symm
    exact hx (nsmul_right_injective (Nat.succ_ne_zero k) h0)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    rw [add_assoc, add_nsmul] at key
    have h0 : (k + 1) • x = (k + 1) • (0 : M) := by
      rw [smul_zero]
      apply add_left_cancel (a := b • x)
      rw [add_zero]
      exact key
    exact hx (nsmul_right_injective (Nat.succ_ne_zero k) h0)
