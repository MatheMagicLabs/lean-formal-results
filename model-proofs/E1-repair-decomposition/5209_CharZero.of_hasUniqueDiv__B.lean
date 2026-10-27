/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CharZero.of_hasUniqueDiv
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Module/Torsion/Free.lean, line 217
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm B, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  have hcancel : ∀ k : ℕ, k ≠ 0 → k • x = 0 → False := by
    intro k hk h
    have hz : k • x = k • (0 : M) := by simpa using h
    apply hx
    first
    | exact nsmul_right_injective hk hz
    | exact nsmul_right_injective (Nat.pos_of_ne_zero hk) hz
    | exact (nsmul_right_inj hk).mp hz
  refine ⟨fun m n h => ?_⟩
  have hsmul : m • x = n • x := by
    simpa only [Nat.cast_smul_eq_nsmul] using
      congrArg (fun r : R => r • x) h
  have hle : ∀ a b : ℕ, a < b → a • x = b • x → False := by
    intro a b hab heq
    have hb : b = a + (b - a) := by omega
    rw [hb, add_nsmul] at heq
    have hz : (b - a) • x = 0 :=
      (add_left_cancel (show a • x + (b - a) • x = a • x + 0 by
        simpa using heq.symm))
    exact hcancel (b - a) (by omega) hz
  rcases lt_trichotomy m n with hlt | heq | hgt
  · exact False.elim (hle m n hlt hsmul)
  · exact heq
  · exact False.elim (hle n m hgt hsmul.symm)
