/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.zpowers_eq_of_isLeast_mem_and_one_lt
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Archimedean.lean, line 43
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem Subgroup.zpowers_eq_of_isLeast_mem_and_one_lt {H : Subgroup G} {a : G}
    (ha : IsLeast { g : G | g ∈ H ∧ 1 < g } a) : zpowers a = H := by
  obtain ⟨⟨a_in, a_pos⟩, a_min⟩ := ha
  refine le_antisymm (Subgroup.zpowers_le.mpr a_in) fun g g_in => ?_
  obtain ⟨k, ⟨hk1, hk2⟩, -⟩ := existsUnique_zpow_near_of_one_lt a_pos g
  have h : g / a ^ k = 1 := by
    by_contra h
    have h1 : 1 < g / a ^ k := lt_of_le_of_ne (one_le_div'.mpr hk1) (Ne.symm h)
    have h2 : a ≤ g / a ^ k := a_min ⟨H.div_mem g_in (H.zpow_mem a_in k), h1⟩
    rw [zpow_add_one] at hk2
    have h3 := le_div_iff_mul_le.mp h2
    rw [mul_comm] at h3
    exact absurd hk2 (not_lt.mpr h3)
  rw [div_eq_one] at h
  rw [h]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) k
