/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_top_iff
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 96
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
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

lemma depth_eq_top_iff (N M : ModuleCat.{v} R) :
    N.depth M = ⊤ ↔ ∀ i, Subsingleton (Ext N M i) := by
  constructor
  · intro h i
    have hS : sSup {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} = ⊤ := h
    rcases (sSup_eq_top.mp hS) (i : ℕ∞) (ENat.natCast_lt_top i) with ⟨a, ha, hi⟩
    exact ha i hi
  · intro h
    apply sSup_eq_top.mpr
    intro b hb
    cases b with
    | top => exact (lt_irrefl ⊤ hb).elim
    | coe n =>
      refine ⟨(n+1 : ℕ∞), ?_, ?_⟩
      · intro j _hj
        exact h j
      · simpa [Nat.cast_succ] using ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self n)
