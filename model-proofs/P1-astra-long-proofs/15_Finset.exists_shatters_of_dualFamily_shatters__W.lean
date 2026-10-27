/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Finset.exists_shatters_of_dualFamily_shatters
Source:      Mathlib @ d0a050ad6, Mathlib/Combinatorics/SetFamily/DualVC.lean, line 115
             (added after the model's training data; human proof 27 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 1 call(s)
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
  have hx : ∀ k : Fin n, ∃ x ∈ X, ∀ b : Fin n → Bool, x ∈ (cube b).val ↔ b k = true := by {
  intro k
  first
  | obtain ⟨u, hu, he⟩ := hS (cubeBitSlice_subset cube k)
  | obtain ⟨u, hu, he⟩ := hS _ (cubeBitSlice_subset cube k)
  obtain ⟨x, hx, rfl⟩ := mem_dualFamily.mp hu
  refine ⟨x, hx, ?_⟩
  intro b
  have hbS : (cube b).val ∈ S := (cube b).property
  have hbA : (cube b).val ∈ 𝒜 := hSA hbS
  have he' := Iff.of_eq (congrArg (fun v : Finset (Finset α) ↦ (cube b).val ∈ v) he)
  simpa only [mem_inter, mem_filter, hbS, hbA, true_and, and_true, mem_cubeBitSlice_iff] using he'
  }
  choose x hxX hx using hx
  have hinj : Function.Injective x := by {
  intro i j hij
  by_contra hne
  let b : Fin n → Bool := fun k ↦ if k = i then true else false
  have hi : x i ∈ (cube b).val := (hx i b).mpr (by simp [b])
  have hj : b j = true := (hx j b).mp (hij ▸ hi)
  simpa [b, Ne.symm hne] using hj
  }
  let T : Finset α := univ.image x
  have hTX : T ⊆ X := by {
  intro a ha
  obtain ⟨k, _, rfl⟩ := mem_image.mp ha
  exact hxX k
  }
  have hTcard : #T = n := by {
  dsimp [T]
  rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  }
  refine ⟨T, hTX, hTcard, ?_⟩
  intro t ht
  let b : Fin n → Bool := fun k ↦ decide (x k ∈ t)
  have htrace : (cube b).val ∩ T = t := by {
  ext a
  simp only [mem_inter]
  constructor
  · rintro ⟨ha, haT⟩
    obtain ⟨k, _, rfl⟩ := mem_image.mp haT
    have hk := (hx k b).mp ha
    simpa [b] using hk
  · intro ha
    have haT := ht ha
    obtain ⟨k, _, hk⟩ := mem_image.mp haT
    refine ⟨?_, haT⟩
    subst a
    exact (hx k b).mpr (by simpa [b] using ha)
  }
  refine ⟨(cube b).val, hSA (cube b).property, ?_⟩
  first
  | exact htrace
  | exact (inter_comm T (cube b).val).trans htrace
