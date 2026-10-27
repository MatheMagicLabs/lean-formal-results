/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     BoundedVariationOn.variation_vectorMeasure_Ioi
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/BoundedVariation.lean, line 453
             (added after the model's training data; human proof 25 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 1 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma variation_vectorMeasure_Ioi (hf : BoundedVariationOn f univ) {a : α} :
    hf.vectorMeasure.variation (Ioi a) = eVariationOn f.rightLim (Ioi a) := by
  have hmono : Monotone (fun b : α ↦ Ioc a b) := fun b c hbc x hx ↦ ⟨hx.1, hx.2.trans hbc⟩
  have hμ := hmono.measure_iUnion (μ := hf.vectorMeasure.variation)
  rw [iUnion_Ioc_right] at hμ
  apply le_antisymm
  · rw [hμ]; exact iSup_le fun b ↦ (variation_vectorMeasure_Ioc hf).le.trans (eVariationOn.mono _ Ioc_subset_Ioi_self)
  · rw [eVariationOn.eq_biSup_inter_Icc]; refine iSup_le fun p ↦ iSup_le fun hp ↦ ?_; calc
      eVariationOn f.rightLim (Ioi a ∩ Icc p.1 p.2) ≤ eVariationOn f.rightLim (Ioc a p.2) := eVariationOn.mono _ (fun x hx ↦ ⟨hx.1, hx.2.2⟩)
      _ = hf.vectorMeasure.variation (Ioc a p.2) := (variation_vectorMeasure_Ioc hf).symm
      _ ≤ hf.vectorMeasure.variation (Ioi a) := measure_mono Ioc_subset_Ioi_self
