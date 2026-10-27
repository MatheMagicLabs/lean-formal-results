/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CharZero.of_hasUniqueDiv
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Module/Torsion/Free.lean, line 217
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  suffices h : ∀ a b : ℕ, a ≤ b → (a : R) = (b : R) → a = b by
    intro a b hab
    rcases le_total a b with hle | hle
    · exact h a b hle hab
    · exact (h b a hle hab.symm).symm
  intro a b hle hab
  by_contra hne
  have hd : b - a ≠ 0 := by omega
  have hinj : Function.Injective (fun x : M => (b - a) • x) := by
    first
    | exact nsmul_right_injective hd
    | exact nsmul_right_injective (b - a) hd
  have he (x : M) : a • x = b • x := by
    simpa only [Nat.cast_smul_eq_nsmul] using
      congrArg (fun r : R => r • x) hab
  have hz (x : M) : (b - a) • x = 0 := by
    apply add_left_cancel (a := a • x)
    rw [← add_nsmul, Nat.add_sub_of_le hle, add_zero, he x]
  obtain ⟨x, y, hxy⟩ := exists_pair_ne M
  exact hxy (hinj ((hz x).trans (hz y).symm))
