/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasurableSpace.exists_eq_iUnion_countablyGeneratedAtom
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/MeasurableSpace/CountablyGenerated.lean, line 192
             (added after the model's training data; human proof 33 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 1 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma exists_eq_iUnion_countablyGeneratedAtom {s : Set α} (hs : MeasurableSet s) :
    ∃ (q : (ℕ → Prop) → Prop), s = ⋃ p, if q p then countablyGeneratedAtom α p else ∅ := by
  classical
  have hsame {x y : α}
      (hy : y ∈ countablyGeneratedAtom α (x ∈ natGeneratingSequence α ·)) :
      x ∈ s ↔ y ∈ s := by
    have hgen : ∀ t ∈ range (natGeneratingSequence α), x ∈ t ↔ y ∈ t := by
      rintro t ⟨n, rfl⟩
      have hyn : y ∈ (if x ∈ natGeneratingSequence α n then
          natGeneratingSequence α n else (natGeneratingSequence α n)ᶜ) :=
        (mem_iInter.mp hy) n
      by_cases hx : x ∈ natGeneratingSequence α n
      · have hy' : y ∈ natGeneratingSequence α n := by
          simpa [hx] using hyn
        exact iff_of_true hx hy'
      · have hy' : y ∉ natGeneratingSequence α n := by
          simpa [hx] using hyn
        exact iff_of_false hx hy'
    exact (forall_generateFrom_mem_iff_mem_iff.mpr hgen) s
      (by rwa [generateFrom_natGeneratingSequence])
  refine ⟨fun p ↦ countablyGeneratedAtom α p ⊆ s, ?_⟩
  ext x
  constructor
  · intro hx
    have hsub : countablyGeneratedAtom α (x ∈ natGeneratingSequence α ·) ⊆ s :=
      fun y hy ↦ (hsame hy).mp hx
    apply mem_iUnion.mpr
    refine ⟨(x ∈ natGeneratingSequence α ·), ?_⟩
    simpa only [if_pos hsub] using
      mem_countablyGeneratedAtom_natGeneratingSequence x
  · intro hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp hx
    by_cases h : countablyGeneratedAtom α p ⊆ s
    · exact h (by simpa only [if_pos h] using hp)
    · simp only [if_neg h, mem_empty_iff_false] at hp
