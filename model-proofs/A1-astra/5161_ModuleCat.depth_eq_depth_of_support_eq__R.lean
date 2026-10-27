/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_depth_of_support_eq
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 157
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 3 (round 0 = first attempt)
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

lemma depth_eq_depth_of_support_eq [IsNoetherianRing R] (I : Ideal R)
    (N M : ModuleCat.{v} R) [Module.Finite R M] [Module.Finite R N]
    [Nontrivial N] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) :
    N.depth M = I.depth M := by
  set_option maxHeartbeats 0 in
    have hvanish (n : ℕ) :
        (∀ i < n, Subsingleton (Ext N M i)) ↔
        (∀ i < n, Subsingleton
          (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i)) := by
      constructor
      · intro h
        apply ((exists_isRegular_tfae I n M smul_lt).out 2 3).mpr
        use N
      · intro h
        have rees := ((exists_isRegular_tfae I n M smul_lt).out 1 2).mpr h
        exact rees N ‹_› ‹_› (le_of_eq hsupp)
    rw [Ideal.depth, depth_eq_sSup_lt_top N M,
      depth_eq_sSup_lt_top (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M]
    apply congrArg sSup
    apply Set.ext
    intro n
    induction n with
    | top => simp
    | coe n => simpa using hvanish n
