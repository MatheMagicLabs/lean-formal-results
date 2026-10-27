/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.mem_zpowers_iff_existsUnique_zpow
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/ArchimedeanDensely.lean, line 44
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma Subgroup.mem_zpowers_iff_existsUnique_zpow {G : Type*}
    [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b : G} (ha : a ≠ 1) :
    b ∈ zpowers a ↔ ∃! k : ℤ, a ^ k = b := by
  have inj : Function.Injective (fun k : ℤ => a ^ k) := by
    rcases ha.lt_or_gt with h | h
    · have h' : 1 < a⁻¹ := one_lt_inv'.mpr h
      have inj' : Function.Injective (fun k : ℤ => a⁻¹ ^ k) := by
        first
          | exact (zpow_right_strictMono h').injective
          | exact (zpow_strictMono_right h').injective
          | exact zpow_right_injective h'
      intro k m hkm
      have h2 : a⁻¹ ^ (-k) = a⁻¹ ^ (-m) := by
        simp only [inv_zpow, zpow_neg, inv_inv]
        simpa using hkm
      have := inj' h2
      omega
    · first
        | exact (zpow_right_strictMono h).injective
        | exact (zpow_strictMono_right h).injective
        | exact zpow_right_injective h
  constructor
  · intro hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    refine ⟨k, rfl, fun m hm => ?_⟩
    exact inj hm
  · rintro ⟨k, hk, _⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hk⟩
