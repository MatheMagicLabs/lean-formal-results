/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.mem_zpowers_iff_existsUnique_zpow
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/ArchimedeanDensely.lean, line 44
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma Subgroup.mem_zpowers_iff_existsUnique_zpow {G : Type*}
    [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b : G} (ha : a ≠ 1) :
    b ∈ zpowers a ↔ ∃! k : ℤ, a ^ k = b := by
  have hinj : Function.Injective (fun n : ℤ => a ^ n) := by
    rcases ha.lt_or_gt with h | h
    · first
        | exact (zpow_right_strictAnti h).injective
        | exact (strictAnti_int_of_succ_lt (fun n => by
            show a ^ (n + 1) < a ^ n
            rw [zpow_add_one]
            exact mul_lt_of_lt_one_right' _ h)).injective
    · first
        | exact (zpow_right_strictMono h).injective
        | exact (strictMono_int_of_lt_succ (fun n => by
            show a ^ n < a ^ (n + 1)
            rw [zpow_add_one]
            exact lt_mul_of_one_lt_right' _ h)).injective
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k, rfl, ?_⟩
    intro k' hk
    exact hinj hk
  · rintro ⟨c, hc, _⟩
    exact ⟨c, hc⟩
