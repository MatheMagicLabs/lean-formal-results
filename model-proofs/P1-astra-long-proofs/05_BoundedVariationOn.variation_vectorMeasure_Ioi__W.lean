/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     BoundedVariationOn.variation_vectorMeasure_Ioi
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/BoundedVariation.lean, line 453
             (added after the model's training data; human proof 25 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 3 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma variation_vectorMeasure_Ioi (hf : BoundedVariationOn f univ) {a : α} :
    hf.vectorMeasure.variation (Ioi a) = eVariationOn f.rightLim (Ioi a) := by
  have : Nonempty α := ⟨a⟩
  apply le_antisymm
  · obtain ⟨u, u_mono, hu⟩ : ∃ u, Monotone u ∧ Tendsto u atTop atTop :=
      Filter.exists_seq_monotone_tendsto_atTop_atTop α
    have hcover : Ioi a = ⋃ n, Ioc a (u n) := by
      ext x
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := (hu.eventually (Ici_mem_atTop x)).exists
        exact mem_iUnion.mpr ⟨n, hx, hn⟩
      · intro hx
        obtain ⟨n, hn⟩ := mem_iUnion.mp hx
        exact hn.1
    have hmono : Monotone (fun n ↦ Ioc a (u n)) := by
      intro i j hij x hx
      exact ⟨hx.1, hx.2.trans (u_mono hij)⟩
    have hlim : Tendsto (fun n ↦ hf.vectorMeasure.variation (Ioc a (u n)))
        atTop (𝓝 (hf.vectorMeasure.variation (Ioi a))) := by
      rw [hcover]
      exact tendsto_measure_iUnion_atTop hmono
    apply le_of_tendsto hlim
    apply Filter.Eventually.of_forall
    intro n
    rw [variation_vectorMeasure_Ioc]
    apply eVariationOn.mono
    exact Ioc_subset_Ioi_self
  · simp only [eVariationOn, iSup_le_iff, Prod.forall, Subtype.forall, mem_Ioi,
      and_imp, edist_eq_enorm_sub]
    intro n u u_mono u_mem
    calc
      ∑ i ∈ Finset.range n,
          ‖Function.rightLim f (u (i + 1)) - Function.rightLim f (u i)‖ₑ
          ≤ ∑ i ∈ Finset.range n,
              hf.vectorMeasure.variation (Ioc (u i) (u (i + 1))) := by
        gcongr with i
        grw [← enorm_measure_le_variation, vectorMeasure_Ioc _ (u_mono (by grind))]
      _ = hf.vectorMeasure.variation
          (⋃ i ∈ Finset.range n, Ioc (u i) (u (i + 1))) := by
        rw [measure_biUnion_finset ?_ (fun i hi ↦ measurableSet_Ioc)]
        rintro i - j - hij
        simp [Function.onFun]
        grind [Monotone]
      _ ≤ hf.vectorMeasure.variation (Ioi a) := measure_mono (by simp; grind)
