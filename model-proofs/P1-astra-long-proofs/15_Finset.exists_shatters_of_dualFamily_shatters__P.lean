/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Finset.exists_shatters_of_dualFamily_shatters
Source:      Mathlib @ d0a050ad6, Mathlib/Combinatorics/SetFamily/DualVC.lean, line 115
             (added after the model's training data; human proof 27 tactic steps)
Experiment:  P1-astra-long-proofs, arm P, solved after 6 call(s)
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
  let cube : (Fin n → Bool) ↪ ↥S := cubeEmbedding S hcard
  have hx : ∃ x : Fin n → α, (∀ k, x k ∈ X) ∧ (∀ (b : Fin n → Bool) (k : Fin n), x k ∈ (cube b).val ↔ b k = true) := by
    have hk : ∀ k : Fin n, ∃ y ∈ X, ∀ b : Fin n → Bool,
        y ∈ (cube b).val ↔ b k = true := by
      intro k
      obtain ⟨u, hu, heq⟩ := hS (cubeBitSlice_subset cube k)
      obtain ⟨y, hy, rfl⟩ := mem_dualFamily.mp hu
      refine ⟨y, hy, ?_⟩
      intro b
      have hbS : (cube b).val ∈ S := (cube b).property
      have hbA : (cube b).val ∈ 𝒜 :=
        subset_of_dualFamily_shatters hS hbS
      have hm := Iff.of_eq (congrArg (fun t => (cube b).val ∈ t) heq)
      simpa only [mem_inter, mem_filter, hbS, hbA, true_and, and_true,
        mem_cubeBitSlice_iff] using hm
    choose x hxX hxbit using hk
    exact ⟨x, hxX, fun b k => hxbit k b⟩
  obtain ⟨x, hxX, hxbit⟩ := hx
  have hxinj : Function.Injective x := by
    intro i j hij
    let b : Fin n → Bool := fun k => decide (k = i)
    have hi : x i ∈ (cube b).val := (hxbit b i).mpr (by simp [b])
    have hj : b j = true := (hxbit b j).mp (hij ▸ hi)
    have hji : j = i := by simpa [b] using hj
    exact hji.symm
  let T : Finset α := Finset.univ.image x
  have hTcard : #T = n := by
    simpa [T] using Finset.card_image_of_injective Finset.univ hxinj
  have hTshatters : 𝒜.Shatters T := by
    intro t ht
    let b : Fin n → Bool := fun k => decide (x k ∈ t)
    refine ⟨(cube b).val, subset_of_dualFamily_shatters hS (cube b).property, ?_⟩
    ext a
    by_cases ha : a ∈ T
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ha
      simpa only [mem_inter, ha, true_and, and_true, hxbit, b,
        decide_eq_true_eq]
    · have hat : a ∉ t := fun h => ha (ht h)
      simp [mem_inter, ha, hat]
  refine ⟨T, ?_, hTcard, hTshatters⟩
  intro a ha
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ha
  exact hxX k
