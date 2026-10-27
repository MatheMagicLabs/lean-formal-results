/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.ramificationIdx_pos_of_mem_minimalPrimes
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/RamificationInertia/Ramification.lean, line 130
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  set_option maxHeartbeats 1000000 in
    let A := Localization.AtPrime q
    let I := p.map (algebraMap R A)
    have hm : IsLocalRing.maximalIdeal A ∈ I.minimalPrimes := by
      dsimp only [I, A]
      rw [IsScalarTower.algebraMap_eq R S (Localization.AtPrime q), ← map_map,
        IsLocalization.minimalPrimes_map q.primeCompl (Localization.AtPrime q)]
      change (IsLocalRing.maximalIdeal (Localization.AtPrime q)).under S ∈
        (p.map (algebraMap R S)).minimalPrimes
      rwa [Localization.AtPrime.under_maximalIdeal]
    rw [ramificationIdx_eq p q]
    change 0 < (Module.length A (A ⧸ I)).toNat
    apply ENat.toNat_pos
    · rw [← pos_iff_ne_zero, Module.length_pos_iff,
        Submodule.Quotient.nontrivial_iff]
      exact (lt_of_le_of_lt hm.1.2
        (IsLocalRing.maximalIdeal.isMaximal A).lt_top).ne
    · rw [Module.length_eq_of_surjective (R := A ⧸ I) Quotient.mk_surjective,
        Module.length_ne_top_iff, ← isArtinianRing_iff_isFiniteLength,
        isArtinianRing_iff_krullDimLE_zero,
        Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal]
      intro J hJ
      haveI : J.IsPrime := hJ.1.1
      have hle : J ≤ IsLocalRing.maximalIdeal A :=
        IsLocalRing.le_maximalIdeal_of_isPrime J
      exact (IsLocalRing.isMaximal_iff A).mpr
        (le_antisymm hle (hm.2 hJ.1 hle))
