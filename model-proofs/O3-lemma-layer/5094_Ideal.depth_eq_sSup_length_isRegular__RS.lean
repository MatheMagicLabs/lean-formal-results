/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.depth_eq_sSup_length_isRegular
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 337
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
    rintro rfl
    simp at smul_lt
  haveI : Nontrivial (R ⧸ I) := (Ideal.Quotient.nontrivial_iff).mpr hI
  let e := Shrink.linearEquiv R (R ⧸ I)
  haveI : Module.Finite R (Shrink.{v} (R ⧸ I)) := Module.Finite.equiv e.symm
  haveI : Nontrivial (Shrink.{v} (R ⧸ I)) := e.toEquiv.nontrivial
  have hsupp : Module.support R (ModuleCat.of R (Shrink.{v} (R ⧸ I))) =
      PrimeSpectrum.zeroLocus I := by
    change Module.support R (Shrink.{v} (R ⧸ I)) = _
    rw [Module.support_eq_zeroLocus, e.annihilator_eq, Ideal.annihilator_quotient]
  haveI : Module.Finite R (ModuleCat.of R (Shrink.{v} (R ⧸ I))) :=
    Module.Finite.equiv e.symm
  haveI : Nontrivial (ModuleCat.of R (Shrink.{v} (R ⧸ I))) := e.toEquiv.nontrivial
  rw [← ModuleCat.depth_eq_depth_of_support_eq I (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M
    smul_lt hsupp]
  exact ModuleCat.depth_eq_sSup_length_isRegular I _ M smul_lt hsupp
