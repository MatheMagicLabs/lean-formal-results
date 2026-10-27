/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsValuativeTopology.of_isInducing
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean, line 237
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem of_isInducing {F : Type*} [FunLike F R S] [RingHomClass F R S] {f : F}
    (hsurj : Function.Surjective f) (hf : IsInducing f) (hv : ∀ a b, f a ≤ᵥ f b ↔ a ≤ᵥ b) :
    IsValuativeTopology R where
  mem_nhds_iff {s x} := by
    have hR : ∀ a b : R, valuation R a ≤ valuation R b ↔ a ≤ᵥ b := by
      intro a b
      first
        | exact (Valuation.Compatible.vle_iff_le (v := valuation R) a b).symm
        | exact (Valuation.Compatible.vle_iff_le a b).symm
        | exact (Valuation.Compatible.rel_iff_le (v := valuation R) a b).symm
        | exact (Valuation.Compatible.rel_iff_le a b).symm
        | simp
    have hS : ∀ a b : S, valuation S a ≤ valuation S b ↔ a ≤ᵥ b := by
      intro a b
      first
        | exact (Valuation.Compatible.vle_iff_le (v := valuation S) a b).symm
        | exact (Valuation.Compatible.vle_iff_le a b).symm
        | exact (Valuation.Compatible.rel_iff_le (v := valuation S) a b).symm
        | exact (Valuation.Compatible.rel_iff_le a b).symm
        | simp
    have hz : ∀ b : R, valuation R b = 0 ↔ valuation S (f b) = 0 := by
      intro b
      have h1 : valuation R b = 0 ↔ valuation R b ≤ valuation R 0 := by
        rw [map_zero]
        exact ⟨fun h => h.le, fun h => le_antisymm h (by first | exact zero_le' | simp)⟩
      have h2 : valuation S (f b) = 0 ↔ valuation S (f b) ≤ valuation S (f 0) := by
        rw [map_zero, map_zero]
        exact ⟨fun h => h.le, fun h => le_antisymm h (by first | exact zero_le' | simp)⟩
      rw [h1, h2, hR, hS, hv]
    have core : ∀ z a b : R, valuation R b ≠ 0 →
        (valuation R z < valuation R a / valuation R b ↔
          valuation S (f z) < valuation S (f a) / valuation S (f b)) := by
      intro z a b hb
      have hb' : valuation S (f b) ≠ 0 := fun h => hb ((hz b).mpr h)
      rw [lt_div_iff₀ (zero_lt_iff.mpr hb), lt_div_iff₀ (zero_lt_iff.mpr hb'),
        ← (valuation R).map_mul, ← (valuation S).map_mul, ← not_le, ← not_le, hR, hS,
        ← map_mul f, hv]
    have surjR : ∀ γ : ValueGroupWithZero R, ∃ (a : R) (b : posSubmonoid R),
        valuation R a / valuation R (b : R) = γ := by
      intro γ
      first
        | exact ValuativeRel.exists_valuation_div_valuation_eq γ
        | exact exists_valuation_div_valuation_eq γ
        | exact ValueGroupWithZero.ind (fun a b => ⟨a, b, by rw [ValueGroupWithZero.mk_eq_div]⟩) γ
        | exact ValueGroupWithZero.ind (fun a b => ⟨a, b, (ValueGroupWithZero.mk_eq_div a b).symm⟩) γ
        | exact ValuativeRel.valuation_surjective γ
        | (induction γ using ValueGroupWithZero.ind with
            | mk a b => exact ⟨a, b, by simp [ValueGroupWithZero.mk_eq_div]⟩)
    have surjS : ∀ γ : ValueGroupWithZero S, ∃ (a : S) (b : posSubmonoid S),
        valuation S a / valuation S (b : S) = γ := by
      intro γ
      first
        | exact ValuativeRel.exists_valuation_div_valuation_eq γ
        | exact exists_valuation_div_valuation_eq γ
        | exact ValueGroupWithZero.ind (fun a b => ⟨a, b, by rw [ValueGroupWithZero.mk_eq_div]⟩) γ
        | exact ValueGroupWithZero.ind (fun a b => ⟨a, b, (ValueGroupWithZero.mk_eq_div a b).symm⟩) γ
        | exact ValuativeRel.valuation_surjective γ
        | (induction γ using ValueGroupWithZero.ind with
            | mk a b => exact ⟨a, b, by simp [ValueGroupWithZero.mk_eq_div]⟩)
    rw [hf.nhds_eq_comap x, Filter.mem_comap]
    constructor
    · rintro ⟨t, ht, hts⟩
      obtain ⟨γ, hγ⟩ := (mem_nhds_iff' (R := S)).mp ht
      obtain ⟨a, b, hab⟩ := surjS (γ : ValueGroupWithZero S)
      obtain ⟨a', rfl⟩ := hsurj a
      obtain ⟨b', hb'⟩ := hsurj (b : S)
      rw [← hb'] at hab
      have hbS : valuation S (f b') ≠ 0 := by
        intro h
        have hb2 := b.2
        rw [← hb'] at hb2
        first
          | exact hb2 ((hS _ _).mp (by rw [h, map_zero]))
          | (simp only [posSubmonoid, Submonoid.mem_mk] at hb2
             exact hb2 ((hS _ _).mp (by rw [h, map_zero])))
          | simp_all
      have hbR : valuation R b' ≠ 0 := fun h => hbS ((hz b').mp h)
      have haS : valuation S (f a') ≠ 0 := by
        intro h
        apply γ.ne_zero
        rw [← hab, h, zero_div]
      have haR : valuation R a' ≠ 0 := fun h => haS ((hz a').mp h)
      refine ⟨Units.mk0 (valuation R a' / valuation R b') (div_ne_zero haR hbR), ?_⟩
      rintro _ ⟨z, hz', rfl⟩
      apply hts
      apply hγ
      show valuation S (f (x + z) - f x) < (γ : ValueGroupWithZero S)
      rw [_root_.map_add f, add_sub_cancel_left, ← hab]
      apply (core z a' b' hbR).mp
      simpa using hz'
    · rintro ⟨γ', hγ'⟩
      obtain ⟨a', b', hab⟩ := surjR (γ' : ValueGroupWithZero R)
      have hbR : valuation R (b' : R) ≠ 0 := by
        intro h
        have hb2 := b'.2
        first
          | exact hb2 ((hR _ _).mp (by rw [h, map_zero]))
          | (simp only [posSubmonoid, Submonoid.mem_mk] at hb2
             exact hb2 ((hR _ _).mp (by rw [h, map_zero])))
          | simp_all
      have haR : valuation R a' ≠ 0 := by
        intro h
        apply γ'.ne_zero
        rw [← hab, h, zero_div]
      have hbS : valuation S (f b') ≠ 0 := fun h => hbR ((hz _).mpr h)
      have haS : valuation S (f a') ≠ 0 := fun h => haR ((hz _).mpr h)
      refine ⟨{w | valuation S (w - f x) <
        (Units.mk0 (valuation S (f a') / valuation S (f b')) (div_ne_zero haS hbS) :
          ValueGroupWithZero S)}, (mem_nhds_iff' (R := S)).mpr ⟨_, subset_rfl⟩, ?_⟩
      intro y hy
      have hy' : valuation S (f y - f x) < valuation S (f a') / valuation S (f b') := by
        simpa using hy
      apply hγ'
      refine ⟨y - x, ?_, by simp⟩
      show valuation R (y - x) < (γ' : ValueGroupWithZero R)
      rw [← hab]
      apply (core (y - x) a' b' hbR).mpr
      rw [_root_.map_sub f]
      exact hy'
