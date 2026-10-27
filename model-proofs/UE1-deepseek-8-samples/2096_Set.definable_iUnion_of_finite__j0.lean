/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Set.definable_iUnion_of_finite
Source:      Mathlib @ d0a050ad6, Mathlib/ModelTheory/Definability.lean, line 156 (group STABLE)
Experiment:  UE1-deepseek-8-samples, arm sample 0, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem definable_iUnion_of_finite {ι : Type*} [Finite ι] {f : ι → Set (α → M)}
    (hf : ∀ i, A.Definable L (f i)) : A.Definable L (⋃ i, f i) := by
  have := Fintype.ofFinite ι
  convert! definable_finset_sup hf Finset.univ using 1
  simp
