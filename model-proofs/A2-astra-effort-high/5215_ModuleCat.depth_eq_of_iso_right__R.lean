/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_of_iso_right
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 184
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

lemma depth_eq_of_iso_right (N : ModuleCat.{v} R) {M M' : ModuleCat.{v} R} (e : M ≅ M') :
    N.depth M = N.depth M' := by
  have transfer (X Y : ModuleCat.{v} R) (f : X ≅ Y) (i : ℕ)
      [Subsingleton (Ext N X i)] : Subsingleton (Ext N Y i) := by
    refine ⟨fun x y => ?_⟩
    have h :
        x.comp (Ext.mk₀ f.inv) (Nat.add_zero i) =
          y.comp (Ext.mk₀ f.inv) (Nat.add_zero i) :=
      Subsingleton.elim _ _
    have h' := congrArg
      (fun z : Ext N X i => z.comp (Ext.mk₀ f.hom) (Nat.add_zero i)) h
    simpa [Ext.comp_assoc] using h'
  have h (i : ℕ) :
      Subsingleton (Ext N M i) ↔ Subsingleton (Ext N M' i) := by
    constructor
    · intro hM
      letI := hM
      exact transfer M M' e i
    · intro hM'
      letI := hM'
      exact transfer M' M e.symm i
  simp only [depth, h]
