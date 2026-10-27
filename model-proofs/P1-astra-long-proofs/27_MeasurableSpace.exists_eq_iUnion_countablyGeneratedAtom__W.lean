/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasurableSpace.exists_eq_iUnion_countablyGeneratedAtom
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/MeasurableSpace/CountablyGenerated.lean, line 192
             (added after the model's training data; human proof 33 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 2 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma exists_eq_iUnion_countablyGeneratedAtom {s : Set α} (hs : MeasurableSet s) :
    ∃ (q : (ℕ → Prop) → Prop), s = ⋃ p, if q p then countablyGeneratedAtom α p else ∅ := by
  classical
  have hsame : ∀ x y : α, (∀ n, x ∈ natGeneratingSequence α n ↔ y ∈ natGeneratingSequence α n) → (x ∈ s ↔ y ∈ s) := by {
  intro x y hxy
  let m : MeasurableSpace α := {
  MeasurableSet' := fun t ↦ x ∈ t ↔ y ∈ t
  measurableSet_empty := Iff.rfl
  measurableSet_compl := fun t ht ↦ not_congr ht
  measurableSet_iUnion := fun f hf ↦ by simpa only [mem_iUnion] using exists_congr hf }
  have hle : generateFrom (range (@natGeneratingSequence α mα _)) ≤ m := by {
  apply generateFrom_le
  intro t ht
  obtain ⟨n, rfl⟩ := ht
  exact hxy n }
  rw [generateFrom_natGeneratingSequence (m := mα)] at hle
  exact hle s hs }
  refine ⟨fun p ↦ ∃ y ∈ s, y ∈ countablyGeneratedAtom α p, ?_⟩
  ext x
  constructor
  · {
  intro hx
  apply mem_iUnion.mpr
  refine ⟨fun n ↦ x ∈ natGeneratingSequence α n, ?_⟩
  have ha := mem_countablyGeneratedAtom_natGeneratingSequence x
  have hq : ∃ y ∈ s, y ∈ countablyGeneratedAtom α (fun n ↦ x ∈ natGeneratingSequence α n) := ⟨x, hx, ha⟩
  simpa only [if_pos hq] using ha }
  · {
  intro hx
  obtain ⟨p, hp⟩ := mem_iUnion.mp hx
  by_cases hq : ∃ y ∈ s, y ∈ countablyGeneratedAtom α p
  · {
  rw [if_pos hq] at hp
  obtain ⟨y, hy, hyp⟩ := hq
  apply (hsame x y ?_).mpr hy
  intro n
  have hx' := (mem_iInter.mp hp) n
  have hy' := (mem_iInter.mp hyp) n
  by_cases hn : p n
  · exact iff_of_true (by simpa [hn] using hx') (by simpa [hn] using hy')
  · exact iff_of_false (by simpa [hn] using hx') (by simpa [hn] using hy') }
  · simp only [if_neg hq, mem_empty_iff_false] at hp }
