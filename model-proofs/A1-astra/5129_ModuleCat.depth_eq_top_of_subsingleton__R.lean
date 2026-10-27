/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_top_of_subsingleton
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 102
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

lemma depth_eq_top_of_subsingleton (N M : ModuleCat.{v} R) [Subsingleton M] :
    N.depth M = ⊤ := by
  have hM : (𝟙 M : M ⟶ M) = 0 := by
    ext x
    exact Subsingleton.elim _ _
  have hz (i : ℕ) (e : Ext N M i) : e = 0 := by
    simpa using congrArg
      (fun f : M ⟶ M => e.comp (Ext.mk₀ f) (Nat.add_zero i)) hM
  unfold depth
  apply top_unique
  apply le_sSup
  intro i hi
  exact ⟨fun a b => (hz i a).trans (hz i b).symm⟩
