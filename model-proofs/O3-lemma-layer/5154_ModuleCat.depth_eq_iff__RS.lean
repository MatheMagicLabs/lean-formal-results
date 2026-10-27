/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_iff
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 124
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

lemma depth_eq_iff (N M : ModuleCat.{v} R) (n : ℕ) : N.depth M = n ↔
    Nontrivial (Ext N M n) ∧ ∀ i < n, Subsingleton (Ext N M i) := by
  classical
  constructor
  · intro h
    have hlt : N.depth M < ⊤ := by rw [h]; exact ENat.coe_lt_top n
    have hex := (depth_lt_top_iff N M).mp hlt
    rw [depth_eq_find N M hex] at h
    have h' := ENat.coe_inj.mp h
    obtain ⟨h1, h2⟩ := (Nat.find_eq_iff hex).mp h'
    exact ⟨h1, fun i hi => not_nontrivial_iff_subsingleton.mp (h2 i hi)⟩
  · rintro ⟨h1, h2⟩
    have hex : ∃ n, Nontrivial (Ext N M n) := ⟨n, h1⟩
    rw [depth_eq_find N M hex]
    exact congrArg _ ((Nat.find_eq_iff hex).mpr
      ⟨h1, fun i hi => not_nontrivial_iff_subsingleton.mpr (h2 i hi)⟩)
