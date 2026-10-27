/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsDedekindDomain.differentIdeal_eq_differentIdeal_mul_differentIdeal_of_isCoprime
Source:      Mathlib @ d0a050ad6, Mathlib/RingTheory/DedekindDomain/LinearDisjoint.lean, line 130 (group DRIFT)
Experiment:  UE1-deepseek-8-samples, arm sample 3, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem differentIdeal_eq_differentIdeal_mul_differentIdeal_of_isCoprime
    [Module.Free A R₂] (h₁ : F₁.LinearDisjoint F₂) (h₂ : F₁ ⊔ F₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) :
    differentIdeal A B = differentIdeal R₁ B * differentIdeal R₂ B := by
  rw [differentIdeal_eq_map_differentIdeal A B R₁ R₂ h₁ h₂ h₃]
  <;> simp [mul_comm]
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
  <;> apply?
  <;> aesop
