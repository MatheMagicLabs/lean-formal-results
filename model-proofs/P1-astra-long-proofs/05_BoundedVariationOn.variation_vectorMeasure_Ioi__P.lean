/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     BoundedVariationOn.variation_vectorMeasure_Ioi
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/BoundedVariation.lean, line 453
             (added after the model's training data; human proof 25 tactic steps)
Experiment:  P1-astra-long-proofs, arm P, solved after 6 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma variation_vectorMeasure_Ioi (hf : BoundedVariationOn f univ) {a : α} :
    hf.vectorMeasure.variation (Ioi a) = eVariationOn f.rightLim (Ioi a) := by
  have hMeasure : hf.vectorMeasure.variation (Ioi a) =
      ⨆ b : α, hf.vectorMeasure.variation (Ioc a b) := by
    haveI : Nonempty α := ⟨a⟩
    obtain ⟨u, hu_mono, hu⟩ : ∃ u : ℕ → α, Monotone u ∧ Tendsto u atTop atTop :=
      Filter.exists_seq_monotone_tendsto_atTop_atTop α
    have hUnion : Ioi a = ⋃ n, Ioc a (u n) := by
      ext x
      simp only [mem_Ioi, mem_iUnion, mem_Ioc]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := (hu.eventually (Ici_mem_atTop x)).exists
        exact ⟨n, hx, hn⟩
      · rintro ⟨n, hx, _⟩
        exact hx
    have hMono : Monotone (fun n ↦ Ioc a (u n)) :=
      fun i j hij ↦ Ioc_subset_Ioc_right (hu_mono hij)
    apply le_antisymm
    · rw [hUnion]
      apply le_of_tendsto (tendsto_measure_iUnion_atTop hMono)
      exact Filter.Eventually.of_forall fun n ↦
        le_iSup (fun b : α ↦ hf.vectorMeasure.variation (Ioc a b)) (u n)
    · exact iSup_le fun b ↦ measure_mono Ioc_subset_Ioi_self
  have hVariation : eVariationOn f.rightLim (Ioi a) =
      ⨆ b : α, eVariationOn f.rightLim (Ioc a b) := by
    apply le_antisymm
    · simp only [eVariationOn, iSup_le_iff, Prod.forall, Subtype.forall,
        mem_Ioi, and_imp]
      intro n u u_mono u_mem
      have hBound := le_iSup
        (fun b : α ↦ eVariationOn f.rightLim (Ioc a b)) (u n)
      simp only [eVariationOn, iSup_le_iff, Prod.forall, Subtype.forall,
        mem_Ioc, and_imp] at hBound
      have h := hBound n (fun i ↦ u (min i n))
        (by
          intro i j hij
          exact u_mono (min_le_min_right n hij))
        (by
          intro i
          exact ⟨u_mem _, u_mono (min_le_right _ _)⟩)
      convert h using 1
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < n := Finset.mem_range.mp hi
      have h₁ : min i n = i := min_eq_left (by omega)
      have h₂ : min (i + 1) n = i + 1 := min_eq_left (by omega)
      simp [h₁, h₂]
    · apply iSup_le
      intro b
      exact eVariationOn.mono _ Ioc_subset_Ioi_self
  rw [hMeasure, hVariation]
  simp_rw [variation_vectorMeasure_Ioc hf]
