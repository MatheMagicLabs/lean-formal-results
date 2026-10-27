/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Set.le_encard_iff_exists_fin_injective
Source:      Mathlib @ a02a63c2, Mathlib/Data/Set/Card.lean, line 494
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
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
    obtain ⟨t, hts, htn⟩ := exists_subset_encard_eq h
    have ht : t.Finite := finite_of_encard_eq_coe htn
    have := ht.fintype
    have hc : Fintype.card t = n := by
      have h2 := coe_fintypeCard t
      rw [htn] at h2
      exact_mod_cast h2
    let e := (Fintype.equivFinOfCardEq hc).symm
    refine ⟨fun i => (e i : α), fun i => hts (e i).2, ?_⟩
    intro i j hij
    exact e.injective (Subtype.ext hij)
  · rintro ⟨f, hfs, hf⟩
    have h1 : ((Finset.univ.map ⟨f, hf⟩ : Finset α) : Set α).encard = n := by
      rw [encard_coe_eq_coe_finsetCard, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    rw [← h1]
    apply encard_le_encard
    intro x hx
    rw [Finset.mem_coe, Finset.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact hfs i
