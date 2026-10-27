/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_depth_of_support_eq
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 157
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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

lemma depth_eq_depth_of_support_eq [IsNoetherianRing R] (I : Ideal R)
    (N M : ModuleCat.{v} R) [Module.Finite R M] [Module.Finite R N]
    [Nontrivial N] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) :
    N.depth M = I.depth M := by
  have (n : ℕ) : (∀ i < n, Subsingleton (Ext N M i)) ↔
      (∀ i < n, Subsingleton (Ext ↧(Shrink.{v} (R ⧸ I)) M i)) := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · apply ((exists_isRegular_tfae I n M smul_lt).out 2 3).mpr
      use N
    · have rees := ((exists_isRegular_tfae I n M smul_lt).out 1 2).mpr h
      exact rees N ‹_› ‹_› (le_of_eq hsupp)
  simp only [depth_eq_sSup_lt_top, Ideal.depth]
  congr
  ext n
  induction n with
  | top => simp
  | coe n => simpa using this n
