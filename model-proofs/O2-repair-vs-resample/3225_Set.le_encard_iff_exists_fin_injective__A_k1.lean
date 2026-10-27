/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Set.le_encard_iff_exists_fin_injective
Source:      Mathlib @ a02a63c2, Mathlib/Data/Set/Card.lean, line 494
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem le_encard_iff_exists_fin_injective (s : Set α) (n : ℕ) :
    (n : ℕ∞) ≤ s.encard ↔ ∃ f : Fin n → α, (∀ i, f i ∈ s) ∧ Function.Injective f := by
  constructor
  · intro h
    obtain ⟨t, hts, ht⟩ := exists_subset_encard_eq h
    have hfin : t.Finite := finite_of_encard_eq_coe ht
    rw [hfin.encard_eq_coe_toFinset_card, Nat.cast_inj] at ht
    let e := Finset.equivFinOfCardEq ht
    refine ⟨fun i => (e.symm i : α), fun i => hts ((hfin.mem_toFinset).1 (e.symm i).2), ?_⟩
    intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  · rintro ⟨f, hfs, hf⟩
    have hsub : ((Finset.univ.map ⟨f, hf⟩ : Finset α) : Set α) ⊆ s := by
      intro x hx
      simp only [Finset.coe_map, Finset.coe_univ, Function.Embedding.coeFn_mk,
        mem_image, mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hfs i
    calc (n : ℕ∞) = ((Finset.univ.map ⟨f, hf⟩ : Finset α) : Set α).encard := by
          rw [encard_coe_eq_coe_finsetCard]; simp
      _ ≤ s.encard := encard_le_encard hsub
