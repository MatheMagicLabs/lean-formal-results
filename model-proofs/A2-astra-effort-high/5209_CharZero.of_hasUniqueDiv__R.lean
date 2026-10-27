/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CharZero.of_hasUniqueDiv
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Module/Torsion/Free.lean, line 217
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  constructor
  intro m n h
  wlog hmn : m ≤ n generalizing m n
  · exact (this h.symm (le_of_not_ge hmn)).symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hh : m • x = (m + k) • x := by
    simpa only [Nat.cast_smul_eq_nsmul] using
      congrArg (fun r : R => r • x) h
  have hk : k • x = 0 := by
    apply add_left_cancel (a := m • x)
    simpa only [add_zero, add_nsmul] using hh.symm
  have hk0 : k = 0 := by
    by_contra hk0
    apply hx
    exact nsmul_right_injective hk0
      (hk.trans (nsmul_zero k).symm)
  simp [hk0]
