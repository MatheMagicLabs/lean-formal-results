/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     BoundedVariationOn.variation_vectorMeasure_Iio
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/BoundedVariation.lean, line 484
             (added after the model's training data; human proof 28 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 2 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma variation_vectorMeasure_Iio (hf : BoundedVariationOn f univ) {a : α} :
    hf.vectorMeasure.variation (Iio a) = eVariationOn f.leftLim (Iio a) := by
  by_cases hb : ∃ (b : α), IsBot b
  · obtain ⟨b, hb⟩ := hb; rw [show Iio a = Ico b a by grind [IsBot], variation_vectorMeasure_Ico]
  apply le_antisymm
  · have : Nonempty α := ⟨a⟩; obtain ⟨u, u_mono, hu⟩ : ∃ u, Antitone u ∧ Tendsto u atTop atBot := Filter.exists_seq_antitone_tendsto_atTop_atBot α; have A : Tendsto (fun n ↦ hf.vectorMeasure.variation (Ico (u n) a)) atTop (𝓝 (hf.vectorMeasure.variation (Iio a))) := by { have : Iio a = ⋃ n, Ico (u n) a := by { apply le_antisymm ?_ (by simp [Ico_subset_Iio_self]); intro x (hx : x < a); simpa [hx] using (hu.eventually (Iic_mem_atBot x)).exists }; rw [this]; exact tendsto_measure_iUnion_atTop (fun i j hij x hx ↦ by grind [Antitone]) }; apply le_of_tendsto A; filter_upwards with n; grw [variation_vectorMeasure_Ico, eVariationOn.mono]; grind
  · simp only [eVariationOn, iSup_le_iff, Prod.forall, Subtype.forall, mem_Iio, and_imp]; intro n u u_mono hu; obtain ⟨b, hb⟩ : ∃ b, b < u 0 := by { simp only [IsBot, not_exists, not_forall, not_le] at hb; exact hb (u 0) }; apply (eVariationOn.sum_le_of_monotoneOn_Iic (s := Ioo b a) (u_mono.monotoneOn _) (by { intro i hi; exact ⟨lt_of_lt_of_le hb (u_mono (Nat.zero_le i)), hu i⟩ })).trans; rw [← variation_vectorMeasure_Ioo_left hf]; exact measure_mono Ioo_subset_Iio_self
