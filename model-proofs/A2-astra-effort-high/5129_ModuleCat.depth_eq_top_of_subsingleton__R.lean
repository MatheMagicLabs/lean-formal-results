/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_top_of_subsingleton
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 102
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

lemma depth_eq_top_of_subsingleton (N M : ModuleCat.{v} R) [Subsingleton M] :
    N.depth M = ⊤ := by
  have hid : (𝟙 M : M ⟶ M) = 0 := by
    ext x
    exact Subsingleton.elim _ _
  unfold depth
  apply top_unique
  apply le_sSup
  intro i hi
  have hz (x : Ext N M i) : x = 0 := by
    have h := congrArg
      (fun f : M ⟶ M => x.comp (Ext.mk₀ f) (Nat.add_zero i)) hid
    simpa using h
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩
