/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CharZero.of_hasUniqueDiv
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Module/Torsion/Free.lean, line 217
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  intro m n h
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have h' : m • x = n • x := by
    simpa only [Nat.cast_smul_eq_nsmul] using
      congrArg (fun r : R => r • x) h
  have hz : ((m : ℤ) - (n : ℤ)) • x = 0 := by
    simpa [sub_smul] using (sub_eq_zero.mpr h' : m • x - n • x = 0)
  have hz' : (m : ℤ) - (n : ℤ) = 0 :=
    (smul_eq_zero.mp hz).resolve_right hx
  exact_mod_cast sub_eq_zero.mp hz'
