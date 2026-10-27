/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.VectorMeasure.semivariation_univ_lt_top
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/Variation/Semivariation.lean, line 133
             (added after the model's training data; human proof 25 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 1 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

private lemma semivariation_univ_lt_top : μ.semivariation univ < ∞ := by
  classical
  by_contra h
  have htop : μ.semivariation univ = ∞ := top_unique (not_lt.mp h)
  let S := {s : Set X // MeasurableSet s ∧ μ.semivariation s = ∞}
  have step (s : S) :
      ∃ t : S, t.val ⊆ s.val ∧ 1 ≤ ‖μ (s.val \ t.val)‖ₑ := by
    obtain ⟨t, ht, hts, htop, hnorm⟩ :=
      exists_one_le_enorm_apply_of_semivariation_eq_top s.property.1 s.property.2
    exact ⟨⟨t, ht, htop⟩, hts, hnorm⟩
  choose f hf using step
  let u : ℕ → S := fun n =>
    Nat.rec ⟨univ, MeasurableSet.univ, htop⟩ (fun _ s => f s) n
  have hu (n : ℕ) :
      (u (n + 1)).val ⊆ (u n).val ∧
        1 ≤ ‖μ ((u n).val \ (u (n + 1)).val)‖ₑ :=
    hf (u n)
  have hm : Antitone (fun n => (u n).val) :=
    antitone_nat_of_succ_le (fun n => (hu n).1)
  have ht := tendsto_vectorMeasure_iInter_atTop_nat (v := μ) hm
    (fun n => (u n).property.1)
  have hd :
      Tendsto (fun n => μ (u n).val - μ (u (n + 1)).val) atTop (𝓝 0) := by
    simpa using ht.sub (ht.comp (tendsto_add_atTop_nat 1))
  have hn :
      Tendsto (fun n => ‖μ (u n).val - μ (u (n + 1)).val‖ₑ) atTop (𝓝 0) := by
    simpa using hd.enorm
  have hle : (1 : ℝ≥0∞) ≤ 0 := by
    apply ge_of_tendsto' hn
    intro n
    simpa only [of_sdiff (u (n + 1)).property.1 (u n).property.1 (hu n).1]
      using (hu n).2
  exact (by simp : ¬ (1 : ℝ≥0∞) ≤ 0) hle
