/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.ramificationIdx_pos_of_mem_minimalPrimes
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/RamificationInertia/Ramification.lean, line 130
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Ideal
section
variable {S : Type*} [CommRing S] (q : Ideal S) (R : Type*) [CommRing R] [Algebra R S]
open scoped Classical in
variable {q R} in
end
section
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

theorem ramificationIdx_pos_of_mem_minimalPrimes [q.LiesOver p] [q.IsPrime]
    (hq : q ∈ (p.map (algebraMap R S)).minimalPrimes)
    [IsNoetherianRing (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)))] :
    0 < q.ramificationIdx R := by
  let Sq := Localization.AtPrime q
  have hmax := IsLocalRing.maximalIdeal.isMaximal Sq
  rw [ramificationIdx_eq p q]
  apply ENat.toNat_pos
  · rw [← pos_iff_ne_zero, Module.length_pos_iff, Submodule.Quotient.nontrivial_iff,
      IsScalarTower.algebraMap_eq R S, ← map_map, ← lt_top_iff_ne_top, q.over_def p]
    grw [map_mono map_comap_le, Localization.AtPrime.map_eq_maximalIdeal, hmax.lt_top]
  · rw [Module.length_eq_of_surjective (R := Sq ⧸ p.map (algebraMap R Sq))
        Quotient.mk_surjective,
      Module.length_ne_top_iff, ← isArtinianRing_iff_isFiniteLength,
      isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
    intro r hr
    apply isMaximal_of_isIntegral_of_isMaximal_under (R := Sq)
    have key : map (algebraMap R S) p ≤ under S r := by
      have := r.ker_le_comap (algebraMap Sq _)
      rw [Ideal.Quotient.algebraMap_eq, mk_ker, map_le_iff_le_comap] at this
      rwa [map_le_iff_le_comap]
    have h1 := hq.2 (y := r.under S) ⟨hr.under S, key⟩
    simp_rw [← Localization.AtPrime.under_maximalIdeal (I := q),
      ← under_under (A := S) (B := Sq) (C := Sq ⧸ _),
      IsLocalization.under_le_under_iff q.primeCompl Sq] at h1
    rwa [← hmax.eq_of_le IsPrime.ne_top'
      (h1 (IsLocalRing.le_maximalIdeal_of_isPrime (r.under Sq)))]
