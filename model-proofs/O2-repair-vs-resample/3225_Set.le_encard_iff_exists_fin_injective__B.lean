/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Set.le_encard_iff_exists_fin_injective
Source:      Mathlib @ a02a63c2, Mathlib/Data/Set/Card.lean, line 494
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem le_encard_iff_exists_fin_injective (s : Set α) (n : ℕ) :
    (n : ℕ∞) ≤ s.encard ↔ ∃ f : Fin n → α, (∀ i, f i ∈ s) ∧ Function.Injective f := by
  classical
  constructor
  · intro h
    obtain ⟨t, hts, ht⟩ := exists_subset_encard_eq h
    have hfin : t.Finite := finite_of_encard_eq_coe ht
    have inst := hfin.fintype
    have hc : Fintype.card t = n := by
      have h2 := coe_fintypeCard t
      rw [ht] at h2
      exact_mod_cast h2
    let e := (Fintype.equivFinOfCardEq hc).symm
    exact ⟨fun i => (e i : α), fun i => hts (e i).2,
      fun i j hij => e.injective (Subtype.ext hij)⟩
  · rintro ⟨f, hf, hinj⟩
    have h1 : ((Finset.univ.image f : Finset α) : Set α).encard = n := by
      rw [encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hinj,
        Finset.card_univ, Fintype.card_fin]
    rw [← h1]
    apply encard_le_encard
    intro x hx
    rw [Finset.coe_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact hf i
