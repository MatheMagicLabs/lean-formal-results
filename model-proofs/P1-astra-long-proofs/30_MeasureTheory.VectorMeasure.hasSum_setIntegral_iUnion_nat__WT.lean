/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.VectorMeasure.hasSum_setIntegral_iUnion_nat
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/SetIntegral.lean, line 471
             (added after the model's training data; human proof 34 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 2 call(s)
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
  have hsum (x : X) :
      HasSum (fun n ↦ (s n).indicator f x) ((⋃ n, s n).indicator f x) := by
    by_cases hx : x ∈ ⋃ n, s n
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      have hz : ∀ j, j ≠ i → (s j).indicator f x = 0 := by
        intro j hji
        apply indicator_of_notMem
        intro hj
        exact Set.disjoint_left.mp (hd hji) hj hi
      simpa only [indicator_of_mem hi, indicator_of_mem hx] using
        (hasSum_single i hz)
    · have hn : ∀ n, x ∉ s n := fun n hn ↦ hx (mem_iUnion.mpr ⟨n, hn⟩)
      simp only [indicator_of_notMem hx, indicator_of_notMem (hn _)]
      exact hasSum_zero
  have hnorm (x : X) :
      HasSum (fun n ↦ (s n).indicator (fun y ↦ ‖f y‖) x)
        ((⋃ n, s n).indicator (fun y ↦ ‖f y‖) x) := by
    by_cases hx : x ∈ ⋃ n, s n
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      have hz : ∀ j, j ≠ i → (s j).indicator (fun y ↦ ‖f y‖) x = 0 := by
        intro j hji
        apply indicator_of_notMem
        intro hj
        exact Set.disjoint_left.mp (hd hji) hj hi
      simpa only [indicator_of_mem hi, indicator_of_mem hx] using
        (hasSum_single i hz)
    · have hn : ∀ n, x ∉ s n := fun n hn ↦ hx (mem_iUnion.mpr ⟨n, hn⟩)
      simp only [indicator_of_notMem hx, indicator_of_notMem (hn _)]
      exact hasSum_zero
  have hmeas : MeasurableSet (⋃ n, s n) := MeasurableSet.iUnion hm
  have hi (n : ℕ) : μ.Integrable ((s n).indicator f) :=
    (hfi.mono hmeas (subset_iUnion s n)).integrable_indicator (hm n)
  have hb : Integrable
      (fun x ↦ ∑' n, (s n).indicator (fun y ↦ ‖f y‖) x) μ.variation := by
    have heq :
        (fun x ↦ ∑' n, (s n).indicator (fun y ↦ ‖f y‖) x) =
          (fun x ↦ ‖(⋃ n, s n).indicator f x‖) := by
      funext x
      rw [(hnorm x).tsum_eq, norm_indicator_eq_indicator_norm]
    rw [heq]
    exact (hfi.integrable_indicator hmeas).norm
  have h := hasSum_integral_of_dominated_convergence
    (B := B) (μ := μ)
    (fun n ↦ (s n).indicator (fun x ↦ ‖f x‖))
    (fun n ↦ (hi n).aestronglyMeasurable)
    (fun n ↦ Eventually.of_forall fun x ↦ by
      rw [norm_indicator_eq_indicator_norm])
    (Eventually.of_forall fun x ↦ (hnorm x).summable)
    hb
    (Eventually.of_forall hsum)
  simpa only [integral_indicator (hm _), integral_indicator hmeas] using h
