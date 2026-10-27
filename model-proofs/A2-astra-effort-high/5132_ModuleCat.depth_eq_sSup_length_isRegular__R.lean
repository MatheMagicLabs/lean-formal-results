/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_sSup_length_isRegular
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 316
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
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

lemma depth_eq_sSup_length_isRegular [IsNoetherianRing R] (I : Ideal R)
    (N M : ModuleCat.{v} R) [Module.Finite R M] [Module.Finite R N]
    [Nontrivial N] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) :
    N.depth M = sSup {(List.length rs : ℕ∞) | (rs : List R)
      (_ : RingTheory.Sequence.IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ I) } := by
  rw [depth_eq_sSup_lt_top]
  congr
  ext m
  simp only [exists_prop]
  refine ⟨fun ⟨lt_top, h⟩ ↦ ?_, fun ⟨rs, reg, mem, len⟩ ↦ ?_⟩
  · rcases ENat.ne_top_iff_exists.mp lt_top.ne with ⟨n, hn⟩
    simp only [← hn, Nat.cast_lt, Nat.cast_inj] at h ⊢
    rcases ((exists_isRegular_tfae I n M smul_lt).out 3 4).mp
      (by use N) with ⟨rs, len, mem, reg⟩
    use rs
  · simp only [← len, ENat.natCast_lt_top, Nat.cast_lt, true_and]
    have rees := ((exists_isRegular_tfae I rs.length M smul_lt).out 4 1).mp
      (by use rs)
    exact rees N ‹_› ‹_› (le_of_eq hsupp)
