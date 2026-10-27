/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MonomialOrder.leadingTerm_pow_of_not_isNilpotent
Source:      Mathlib @ d0a050ad6, Mathlib/RingTheory/MvPolynomial/MonomialOrder.lean, line 611 (group STABLE)
Experiment:  UE1-deepseek-8-samples, arm sample 1, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem leadingTerm_pow_of_not_isNilpotent {f : MvPolynomial σ R} (n : ℕ)
    (h : ¬IsNilpotent (m.leadingCoeff f)) :
    m.leadingTerm (f ^ n) = m.leadingTerm f ^ n := by
  simp [leadingTerm, leadingCoeff_pow_of_not_isNilpotent n h, degree_pow_of_not_isNilpotent n h,
    monomial_pow]
