/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_sSup_length_isRegular
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 316
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
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

lemma depth_eq_sSup_length_isRegular [IsNoetherianRing R] (I : Ideal R)
    (N M : ModuleCat.{v} R) [Module.Finite R M] [Module.Finite R N]
    [Nontrivial N] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) :
    N.depth M = sSup {(List.length rs : ℕ∞) | (rs : List R)
      (_ : RingTheory.Sequence.IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ I) } := by
  rw [depth_eq_sSup_lt_top N M]
  congr 1
  ext m
  constructor
  · rintro ⟨hlt, h⟩
    obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.mp hlt.ne
    have h' : ∀ i < k, Subsingleton (Ext N M i) := fun i hi => h i (by exact_mod_cast hi)
    obtain ⟨rs, hrs⟩ := exists_isRegular_of_exists_subsingleton_ext I k M smul_lt N hsupp h'
    clear h h' hlt
    refine ⟨rs, ?_, ?_, ?_⟩
    · tauto
    · tauto
    · have hl : rs.length = k := by tauto
      rw [hl]
  · rintro ⟨rs, reg, mem, rfl⟩
    refine ⟨ENat.coe_lt_top _, fun i hi => ?_⟩
    have hi' : i < rs.length := by exact_mod_cast hi
    apply subsingleton_ext_of_exists_isRegular I N hsupp.le M smul_lt rs
    all_goals first | assumption | exact hi' | exact_mod_cast hi
