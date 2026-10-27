/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Finset.exists_shatters_of_dualFamily_shatters
Source:      Mathlib @ d0a050ad6, Mathlib/Combinatorics/SetFamily/DualVC.lean, line 115
             (added after the model's training data; human proof 27 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 1 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem exists_shatters_of_dualFamily_shatters
    (𝒜 : Finset (Finset α)) (X : Finset α)
    {S : Finset (Finset α)} (hS : (𝒜.dualFamily X).Shatters S)
    {n : ℕ} (hcard : 2 ^ n ≤ #S) :
    ∃ T : Finset α, T ⊆ X ∧ #T = n ∧ 𝒜.Shatters T := by
  classical
  let cube := cubeEmbedding S hcard
  have hSA : S ⊆ 𝒜 := subset_of_dualFamily_shatters hS
  have hex : ∀ k : Fin n, ∃ x ∈ X,
      ∀ b : Fin n → Bool, x ∈ (cube b).val ↔ b k = true := by
    intro k
    obtain ⟨u, hu, heq⟩ := hS (cubeBitSlice_subset cube k)
    obtain ⟨x, hx, rfl⟩ := mem_dualFamily.mp hu
    refine ⟨x, hx, ?_⟩
    intro b
    rw [← mem_cubeBitSlice_iff cube b k, ← heq]
    simp only [mem_inter, mem_filter]
    simp [(cube b).property, hSA (cube b).property]
  choose x hxX hx using hex
  have hinj : Function.Injective x := by
    intro i j hij
    let b : Fin n → Bool := fun k ↦ decide (k = i)
    have hi : x i ∈ (cube b).val := (hx i b).mpr (by simp [b])
    have hj : x j ∈ (cube b).val := by
      rw [← hij]
      exact hi
    have hji : j = i := by
      simpa [b] using (hx j b).mp hj
    exact hji.symm
  refine ⟨univ.image x, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨k, _, rfl⟩ := mem_image.mp ha
    exact hxX k
  · rw [card_image_of_injective univ hinj]
    simp
  · intro t ht
    let b : Fin n → Bool := fun k ↦ decide (x k ∈ t)
    refine ⟨(cube b).val, hSA (cube b).property, ?_⟩
    apply subset_antisymm
    · intro a ha
      obtain ⟨k, _, rfl⟩ := mem_image.mp (mem_inter.mp ha).1
      have hk := (hx k b).mp (mem_inter.mp ha).2
      simpa [b] using hk
    · intro a ha
      have haT := ht ha
      obtain ⟨k, _, rfl⟩ := mem_image.mp haT
      refine mem_inter.mpr ⟨haT, (hx k b).mpr ?_⟩
      simpa [b] using ha
