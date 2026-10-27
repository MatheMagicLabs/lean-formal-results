/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.ramificationIdx_pos_of_mem_minimalPrimes
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/RamificationInertia/Ramification.lean, line 130
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  have h := ramificationIdx_eq (p := p) (q := q) (R := R)
  try dsimp only at h
  rw [h]
  have hJ : (p.map (algebraMap R (Localization.AtPrime q))).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    have := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
      (A := Localization.AtPrime q) q _ hq
    rwa [Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      Localization.AtPrime.map_eq_maximalIdeal] at this
  have hJle : p.map (algebraMap R (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := hJ ▸ Ideal.le_radical
  have hdim : Ring.KrullDimLE 0
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) := by
    have H : ∀ P : Ideal (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))),
        P.IsPrime → P.IsMaximal := by
      intro P hP
      have hle : p.map (algebraMap R (Localization.AtPrime q)) ≤ P.comap (Ideal.Quotient.mk _) :=
        fun x hx => by
          rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact P.zero_mem
      have h1 : P.comap (Ideal.Quotient.mk (p.map (algebraMap R (Localization.AtPrime q)))) =
          IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
        apply le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.comap_isPrime _ P).ne_top)
        rw [← hJ]
        exact (Ideal.radical_mono hle).trans (Ideal.comap_isPrime _ P).radical.le
      have h2 := Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P
      rw [h1] at h2
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective
          (f := Ideal.Quotient.mk (p.map (algebraMap R (Localization.AtPrime q))))
          Ideal.Quotient.mk_surjective (IsLocalRing.maximalIdeal.isMaximal _) with h3 | h3
      · exact absurd (h2.symm.trans h3) hP.ne_top
      · rw [← h2]; exact h3
    first
      | exact Ring.KrullDimLE.mk₀ H
      | exact Ring.krullDimLE_zero_iff.mpr H
  haveI : IsArtinianRing
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr ⟨inferInstance, hdim⟩
  let e : Submodule (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)))
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) ≃o
      Submodule (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) :=
    RelIso.ofSurjective (Submodule.restrictScalarsEmbedding _ _ _) (by
      intro N
      refine ⟨⟨N.toAddSubmonoid, ?_⟩, rfl⟩
      intro a x hx
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
      have : Ideal.Quotient.mk (p.map (algebraMap R (Localization.AtPrime q))) s • x = s • x := by
        simp only [Algebra.smul_def]; rfl
      rw [this]; exact N.smul_mem s hx)
  haveI : IsArtinian (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) := by
    first
      | exact e.symm.strictMono.wellFoundedLT
      | exact e.symm.toOrderEmbedding.wellFoundedLT
  haveI : IsNoetherian (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) := by
    first
      | exact isNoetherian_iff'.mpr e.symm.strictMono.wellFoundedGT
      | exact isNoetherian_iff'.mpr e.symm.toOrderEmbedding.wellFoundedGT
  have hfin : Module.length (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
  haveI : Nontrivial
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hJle)
  have hpos : 0 < Module.length (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) :=
    Module.length_pos
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hn] at hpos ⊢
  simp only [ENat.toNat_coe]
  exact_mod_cast hpos
