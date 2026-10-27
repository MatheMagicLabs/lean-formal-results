/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Algebra.IsAlgebraic.rank_fractionRing_mvPolynomial
Source:      Mathlib @ d0a050ad6, Mathlib/RingTheory/Algebraic/Integral.lean, line 678 (group DRIFT)
Experiment:  UE1-deepseek-8-samples, arm sample 6, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
@[stacks 0G1M] theorem rank_fractionRing_mvPolynomial (σ : Type u) :
    Module.rank (FractionRing (MvPolynomial σ R)) (FractionRing (MvPolynomial σ S)) =
    lift.{u} (Module.rank R S) := by
  have := IsDomain.of_faithfulSMul R S
  rw [rank_fractionRing, rank_mvPolynomial_mvPolynomial]
  <;> simp_all
  <;> apply lift_id
  <;> apply lift_umax
