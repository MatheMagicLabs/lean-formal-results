/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_of_iso_right
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 184
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  have transfer {A B : ModuleCat.{v} R} (e : A ≅ B) (i : ℕ)
      [Subsingleton (Ext N A i)] : Subsingleton (Ext N B i) := by
    let f : Ext N B i → Ext N A i :=
      fun x => x.comp (Ext.mk₀ e.inv) (by omega)
    have hf : Function.Injective f := by
      intro x y h
      have h' := congrArg
        (fun z : Ext N A i => z.comp (Ext.mk₀ e.hom) (show i + 0 = i by omega)) h
      simpa [f, Ext.comp_assoc] using h'
    exact hf.subsingleton
  have h (i : ℕ) :
      Subsingleton (Ext N M i) ↔ Subsingleton (Ext N M' i) := by
    constructor
    · intro h
      letI := h
      exact transfer e i
    · intro h
      letI := h
      exact transfer e.symm i
  simp only [depth, h]
