/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     surjective_of_isLocalization_of_span_eq_top
Source:      Mathlib @ d0a050ad6, Mathlib/RingTheory/LocalProperties/Exactness.lean, line 310 (group DRIFT)
Experiment:  D1-deepseek-16-samples, arm sample 0, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 16 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma surjective_of_isLocalization_of_span_eq_top
    (h : ∀ r : s, Function.Surjective (IsLocalization.Away.map (Rᵣ r) (Sᵣ r) f r.1)) :
    Function.Surjective f := by
  algebraize [f]
  let (r : s) : Algebra R (Sᵣ r) := (algebraMap S (Sᵣ r)).comp f |>.toAlgebra
  have (r : s) : IsScalarTower R S (Sᵣ r) := IsScalarTower.of_algebraMap_eq' rfl
  have : ∀ r, IsLocalization.Away (algebraMap R S r.val) (Sᵣ r) := ‹_›
  let (r : s) : Algebra (Rᵣ r) (Sᵣ r) := localizationAlgebra (.powers r.val) S
  have (r : s) : IsScalarTower R (Rᵣ r) (Sᵣ r) :=
    .of_algebraMap_eq <| by simp [RingHom.algebraMap_toAlgebra]
  apply surjective_of_isLocalized_span s hs Rᵣ (fun r : s ↦ Algebra.linearMap _ _) _
    (fun r : s ↦ ((IsScalarTower.toAlgHom R S (Sᵣ r)).toLinearMap)) (Algebra.linearMap R S)
  simpa [IsLocalization.map_linearMap_eq_toLinearMap_mapₐ] using! h
