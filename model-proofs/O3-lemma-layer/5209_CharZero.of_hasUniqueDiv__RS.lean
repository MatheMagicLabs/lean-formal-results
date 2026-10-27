/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CharZero.of_hasUniqueDiv
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Module/Torsion/Free.lean, line 217
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
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
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have key : ∀ m n : ℕ, (m : R) = n → m ≤ n → m = n := by
    intro m n h hle
    by_contra hne
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hk : k ≠ 0 := by omega
    have h1 : ((m + k : ℕ) : R) • x = (m : R) • x := by rw [h]
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, add_nsmul] at h1
    have h2 : k • x = k • (0 : M) := by
      rw [smul_zero]
      exact add_left_cancel (h1.trans (add_zero _).symm)
    exact hx ((IsSMulRegular.nat_of_hasUniqueDiv hk) h2)
  rcases le_total a b with h | h
  · exact key a b hab h
  · exact (key b a hab.symm h).symm
