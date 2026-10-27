/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.mem_zpowers_iff_existsUnique_zpow
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/ArchimedeanDensely.lean, line 44
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma Subgroup.mem_zpowers_iff_existsUnique_zpow {G : Type*}
    [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b : G} (ha : a ≠ 1) :
    b ∈ zpowers a ↔ ∃! k : ℤ, a ^ k = b := by
  rw [mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k, rfl, ?_⟩
    intro k' hk'
    first
      | exact zpow_right_injective ha hk'
      | (have h1 : a ^ (k' - k) = 1 := by
           rw [zpow_sub, hk', mul_inv_cancel]
         have h2 := (zpow_eq_one_iff_right ha).mp h1
         omega)
      | (rcases ha.lt_or_gt with h | h
         · exact (zpow_right_strictAnti h).injective hk'
         · exact (zpow_right_strictMono h).injective hk')
  · rintro ⟨k, rfl, -⟩
    exact ⟨k, rfl⟩
