/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CategoryTheory.Presheaf.uliftYonedaAdjunction_unit_app_app
Source:      Mathlib @ d0a050ad6, Mathlib/CategoryTheory/Limits/Presheaf.lean, line 209 (group STABLE)
Experiment:  UE1-deepseek-8-samples, arm sample 7, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma uliftYonedaAdjunction_unit_app_app (P : Cᵒᵖ ⥤ Type max w v₁ v₂)
    {Z : Cᵒᵖ} (z : P.obj Z) :
    dsimp% ((uliftYonedaAdjunction.{w} L α).unit.app P).app Z z =
      ULift.up (α.app Z.unop ≫ L.map (uliftYonedaEquiv.symm z)) := by
  simp [uliftYonedaAdjunction, restrictedULiftYonedaHomEquiv,
    restrictedULiftYonedaHomEquiv', IsColimit.homEquiv]
  <;> aesop_cat
