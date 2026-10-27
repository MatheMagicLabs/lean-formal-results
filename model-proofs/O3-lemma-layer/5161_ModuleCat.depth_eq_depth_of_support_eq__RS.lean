/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_depth_of_support_eq
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 157
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 2 (round 0 = first attempt)
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

lemma depth_eq_depth_of_support_eq [IsNoetherianRing R] (I : Ideal R)
    (N M : ModuleCat.{v} R) [Module.Finite R M] [Module.Finite R N]
    [Nontrivial N] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) :
    N.depth M = I.depth M := by
  show N.depth M = (ModuleCat.of R (Shrink.{v} (R ⧸ I))).depth M
  have key : ∀ n : ℕ, (∀ i < n, Subsingleton (Ext N M i)) ↔
      (∀ i < n, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i)) := by
    intro n
    have tfae := exists_isRegular_tfae I n M smul_lt
    constructor
    · intro hL
      have h := tfae _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      exact h.mp ⟨N, inferInstance, inferInstance, hsupp, hL⟩
    · intro hS
      have h := tfae _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        _ (List.mem_cons_self ..)
      exact h.mp hS N inferInstance inferInstance hsupp.le
  rw [depth_eq_sSup_lt_top, depth_eq_sSup_lt_top]
  congr 1
  ext n
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    lift n to ℕ using hn.ne
    have := (key n).mp (fun i hi => h i (by exact_mod_cast hi))
    intro i hi
    exact this i (by exact_mod_cast hi)
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    lift n to ℕ using hn.ne
    have := (key n).mpr (fun i hi => h i (by exact_mod_cast hi))
    intro i hi
    exact this i (by exact_mod_cast hi)
