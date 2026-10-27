/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.depth_eq_sSup_length_isRegular
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 337
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open IsLocalRing LinearMap Module
universe v u
open RingTheory.Sequence Ideal CategoryTheory Abelian Limits Pointwise ModuleCat IsSMulRegular
variable {R : Type u} [CommRing R] [Small.{v} R]
section depth
namespace ModuleCat
open Classical in
end ModuleCat

lemma Ideal.depth_eq_sSup_length_isRegular [IsNoetherianRing R] (I : Ideal R)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤) :
    I.depth M = sSup {(List.length rs : ℕ∞) | (rs : List R)
      (_ : IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ I)} := by
  have hI : I ≠ ⊤ := by
    intro h
    simpa [h] using smul_lt
  letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  let e : (R ⧸ I) ≃ₗ[R] Shrink.{v} (R ⧸ I) := by
    first
    | exact Shrink.linearEquiv R (R ⧸ I)
    | exact (Shrink.linearEquiv R (R ⧸ I)).symm
  have hann : annihilator R (Shrink.{v} (R ⧸ I)) = I := by
    ext r
    simp only [Module.mem_annihilator]
    constructor
    · intro h
      have hy : r • (1 : R ⧸ I) = 0 := by
        apply e.injective
        simpa only [map_smul, map_zero] using h (e 1)
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change Ideal.Quotient.mk I r * 1 = 0 at hy
      simpa only [mul_one] using hy
    · intro hr x
      obtain ⟨y, rfl⟩ := e.surjective x
      have hz : Ideal.Quotient.mk I r = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hr
      have hy : r • y = 0 := by
        change Ideal.Quotient.mk I r * y = 0
        rw [hz, zero_mul]
      rw [← e.map_smul, hy, map_zero]
  simpa [Ideal.depth] using
    (ModuleCat.depth_eq_sSup_length_isRegular I
      (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M smul_lt
      (by simpa [Module.support_eq_zeroLocus, hann]))
