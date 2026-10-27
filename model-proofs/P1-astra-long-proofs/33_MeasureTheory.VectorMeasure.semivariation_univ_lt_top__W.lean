/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.VectorMeasure.semivariation_univ_lt_top
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/Variation/Semivariation.lean, line 133
             (added after the model's training data; human proof 25 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 5 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

private lemma semivariation_univ_lt_top : μ.semivariation univ < ∞ := by
  classical
  by_contra h
  have htop : μ.semivariation univ = ∞ := top_unique (le_of_not_gt h)
  let S := {s : Set X // MeasurableSet s ∧ μ.semivariation s = ∞}
  have hstep : ∀ s : S, ∃ t : S, t.val ⊆ s.val ∧ 1 ≤ ‖μ (s.val \ t.val)‖ₑ := by {
  intro s
  obtain ⟨t, ht, hts, ht_top, ht_norm⟩ := exists_one_le_enorm_apply_of_semivariation_eq_top s.2.1 s.2.2
  exact ⟨⟨t, ht, ht_top⟩, hts, ht_norm⟩ }
  choose f hf using hstep
  let u : ℕ → S := Nat.rec ⟨univ, MeasurableSet.univ, htop⟩ (fun _ s => f s)
  let v : ℕ → Set X := fun n => (u n).val
  have hsub (n : ℕ) : v (n + 1) ⊆ v n := by {
  change (f (u n)).val ⊆ (u n).val
  exact (hf (u n)).1 }
  have hanti : Antitone v := by {
  apply antitone_nat_of_succ_le
  intro n
  exact hsub n }
  let d : ℕ → Set X := fun n => v n \ v (n + 1)
  have hd_meas (n : ℕ) : MeasurableSet (d n) := (u n).2.1.diff (u (n + 1)).2.1
  have hd_norm (n : ℕ) : 1 ≤ ‖μ (d n)‖ₑ := (hf (u n)).2
  have hd_lt : ∀ i j : ℕ, i < j → Disjoint (d i) (d j) := by {
  intro i j hij
  apply Set.disjoint_left.2
  intro x hxi hxj
  exact hxi.2 (hanti (Nat.succ_le_of_lt hij) hxj.1) }
  have hd : Pairwise (Disjoint on d) := by {
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact hd_lt i j hij
  · exact (hd_lt j i hij).symm }
  have hsum : Summable (fun n => μ (d n)) := by {
  first
  | exact (μ.of_disjoint_iUnion hd_meas hd).summable
  | exact (μ.of_disjoint_iUnion hd hd_meas).summable
  | exact (μ.m_iUnion hd_meas hd).summable
  | exact (μ.m_iUnion hd hd_meas).summable
  | exact (μ.m_iUnion' d hd_meas hd).summable }
  have hlim : Tendsto (fun n => ‖μ (d n)‖) atTop (𝓝 (0 : ℝ)) := by {
  simpa using hsum.tendsto_atTop_zero.norm }
  have hnorm (n : ℕ) : (1 : ℝ) ≤ ‖μ (d n)‖ := by {
  have hn := hd_norm n
  rw [enorm_eq_nnnorm] at hn
  exact_mod_cast hn }
  have hbad : (1 : ℝ) ≤ 0 := ge_of_tendsto hlim (Filter.Eventually.of_forall hnorm)
  norm_num at hbad
