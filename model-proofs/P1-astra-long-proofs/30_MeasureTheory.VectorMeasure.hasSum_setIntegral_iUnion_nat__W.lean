/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.VectorMeasure.hasSum_setIntegral_iUnion_nat
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/SetIntegral.lean, line 471
             (added after the model's training data; human proof 34 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 4 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

private theorem hasSum_setIntegral_iUnion_nat {s : ℕ → Set X}
    (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hfi : μ.IntegrableOn f (⋃ i, s i)) :
    HasSum (fun n ↦ ∫ᵛ x in s n, f x ∂[B; μ]) (∫ᵛ x in ⋃ n, s n, f x ∂[B; μ]) := by
  classical
  let ν := μ.restrict (⋃ i, s i)
  have hf : Integrable f ν.variation := hfi
  have hsingle (t : Finset ℕ) (i : ℕ) (hi : i ∈ t) (x : X) (hx : x ∈ s i) : (∑ j ∈ t, (s j).indicator f x) = f x := by
  {
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem hx f
  · intro j hj hji; exact indicator_of_notMem (fun hxj ↦ Set.disjoint_left.1 (hd hji) hxj hx) f
  · exact fun h ↦ (h hi).elim
  }
  have h_int (t : Finset ℕ) : Integrable (fun x ↦ ∑ i ∈ t, (s i).indicator f x) ν.variation := by
  {
  induction t using Finset.induction_on with
  | empty => simpa using (integrable_zero X E ν.variation)
  | @insert i t hi ih => convert! (hf.indicator (hm i)).add ih using 1 <;> ext x <;> simp [Finset.sum_insert hi]
  }
  have hbound (t : Finset ℕ) (x : X) : ‖∑ i ∈ t, (s i).indicator f x‖ ≤ ‖f x‖ := by
  {
  by_cases hx : ∃ i ∈ t, x ∈ s i
  · obtain ⟨i, hi, hx⟩ := hx; rw [hsingle t i hi x hx]
  · have hz : (∑ i ∈ t, (s i).indicator f x) = 0 := Finset.sum_eq_zero (fun i hi ↦ indicator_of_notMem (fun h ↦ hx ⟨i, hi, h⟩) f); rw [hz, norm_zero]; exact norm_nonneg _
  }
  have hlim : ∀ᵐ x ∂ν.variation, Tendsto (fun t : Finset ℕ ↦ ∑ i ∈ t, (s i).indicator f x) atTop (𝓝 (f x)) := by
  {
  have hmem : ∀ᵐ x ∂ν.variation, x ∈ ⋃ i, s i := by
  {
  dsimp [ν]
  rw [variation_restrict (MeasurableSet.iUnion hm)]
  exact ae_restrict_mem (MeasurableSet.iUnion hm)
  }
  filter_upwards [hmem] with x hx
  obtain ⟨i, hi⟩ := mem_iUnion.1 hx
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_atTop.2 ⟨{i}, fun t ht ↦ ht (Finset.mem_singleton_self i)⟩] with t ht
  exact (hsingle t i ht x hi).symm
  }
  have hconv := tendsto_integral_filter_of_dominated_convergence (B := B) (μ := ν) (fun x ↦ ‖f x‖) (Eventually.of_forall fun t ↦ (h_int t).aestronglyMeasurable) (Eventually.of_forall fun t ↦ Eventually.of_forall (hbound t)) hf.norm hlim
  have heq (i : ℕ) : (∫ᵛ x, (s i).indicator f x ∂[B; ν]) = ∫ᵛ x in s i, f x ∂[B; μ] := by
  {
  rw [integral_indicator (hm i)]
  simp [ν, restrict_restrict, hm, MeasurableSet.iUnion, inter_eq_left.mpr (subset_iUnion s i), inter_eq_right.mpr (subset_iUnion s i)]
  }
  have hsum (t : Finset ℕ) : (∫ᵛ x, (∑ i ∈ t, (s i).indicator f x) ∂[B; ν]) = ∑ i ∈ t, ∫ᵛ x in s i, f x ∂[B; μ] := by
  {
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih => simp only [Finset.sum_insert hi]; rw [integral_fun_add (hf.indicator (hm i)) (h_int t), heq i, ih]
  }
  change Tendsto (fun t : Finset ℕ ↦ ∑ i ∈ t, ∫ᵛ x in s i, f x ∂[B; μ]) atTop (𝓝 (∫ᵛ x, f x ∂[B; ν]))
  simpa only [hsum] using hconv
