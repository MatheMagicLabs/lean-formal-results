/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.depth_eq_sSup_length_isRegular
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 337
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : Module.Finite R (Shrink.{v} (R ⧸ I)) :=
    Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm
  haveI : Nontrivial (Shrink.{v} (R ⧸ I)) :=
    (Shrink.linearEquiv R (R ⧸ I)).toEquiv.nontrivial
  unfold Ideal.depth
  apply ModuleCat.depth_eq_sSup_length_isRegular I _ M smul_lt
  show Module.support R (Shrink.{v} (R ⧸ I)) = _
  rw [(Shrink.linearEquiv R (R ⧸ I)).support_eq, Module.support_of_algebra,
    Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
