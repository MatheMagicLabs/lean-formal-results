/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_sSup_length_isRegular
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 316
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 0 (round 0 = first attempt)
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

lemma depth_eq_sSup_length_isRegular [IsNoetherianRing R] (I : Ideal R)
    (N M : ModuleCat.{v} R) [Module.Finite R M] [Module.Finite R N]
    [Nontrivial N] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) :
    N.depth M = sSup {(List.length rs : ℕ∞) | (rs : List R)
      (_ : RingTheory.Sequence.IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ I) } := by
  rw [depth_eq_sSup_lt_top]
  congr 1
  ext n
  constructor
  · rintro ⟨hn, h⟩
    lift n to ℕ using hn.ne
    obtain ⟨rs, h₁, h₂, h₃⟩ :=
      exists_isRegular_of_exists_subsingleton_ext I n M smul_lt N hsupp
        (by
          intro i hi
          exact h i (by exact_mod_cast hi))
    have hlen : rs.length = n := by
      first | assumption | exact Eq.symm (by assumption)
    have hreg : RingTheory.Sequence.IsRegular M rs := by assumption
    have hmem : ∀ r ∈ rs, r ∈ I := by assumption
    exact ⟨rs, hreg, hmem, by simp only [hlen]⟩
  · rintro ⟨rs, hreg, hmem, rfl⟩
    refine ⟨by simp, ?_⟩
    intro i hi
    apply subsingleton_ext_of_exists_isRegular I N (le_of_eq hsupp)
      M smul_lt rs hmem hreg
    exact_mod_cast hi
