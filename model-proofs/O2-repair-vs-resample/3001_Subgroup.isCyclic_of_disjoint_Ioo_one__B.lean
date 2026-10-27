/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.isCyclic_of_disjoint_Ioo_one
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/ArchimedeanDensely.lean, line 107
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem Subgroup.isCyclic_of_disjoint_Ioo_one {G : Type*} [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] [MulArchimedean G] {H : Subgroup G} {a : G} (h₀ : 1 < a)
    (hd : Disjoint (H : Set G) (Ioo 1 a)) : IsCyclic H := by
  rcases eq_or_ne H ⊥ with rfl | hbot
  · infer_instance
  · first
    | (obtain ⟨b, hb⟩ := Subgroup.exists_isLeast_one_lt hbot h₀ hd
       rw [Subgroup.cyclic_of_min hb, ← Subgroup.zpowers_eq_closure]
       infer_instance)
    | (obtain ⟨b, ⟨hbH, hb1⟩, hmin⟩ := Subgroup.exists_isLeast_one_lt hbot h₀ hd
       refine ⟨⟨⟨b, hbH⟩, fun x => ?_⟩⟩
       obtain ⟨k, ⟨hk1, hk2⟩, -⟩ := existsUnique_zpow_near_of_one_lt hb1 (x : G)
       refine ⟨k, Subtype.ext ?_⟩
       show b ^ k = (x : G)
       have hc : (x : G) * (b ^ k)⁻¹ ∈ H := H.mul_mem x.2 (H.inv_mem (H.zpow_mem hbH k))
       have h1 : 1 ≤ (x : G) * (b ^ k)⁻¹ := by
         rw [le_mul_inv_iff_mul_le, one_mul]; exact hk1
       have h2 : (x : G) * (b ^ k)⁻¹ < b := by
         rw [mul_inv_lt_iff_lt_mul, mul_comm b, ← zpow_add_one]; exact hk2
       rcases h1.lt_or_eq with h1 | h1
       · exact absurd (hmin ⟨hc, h1⟩) (not_le.2 h2)
       · rw [eq_comm, mul_inv_eq_one] at h1; exact h1.symm)
