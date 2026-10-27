/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFClass.cmem_sInter
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 139
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

universe u
namespace ZFClass
variable {A B C : ZFClass.{u}} {x y : ZFSet.{u}}
scoped notation:50 A:50 " ᶜ∈ " B:50 => ZFClass.CMem A B
scoped notation:50 A:50 " ᶜ∉ " B:50 => ¬ ZFClass.CMem A B
scoped under the `ZFClass` namespace. -/
scoped prefix:110 "⋃₀ " => ZFClass.sUnion
scoped prefix:110 "⋂₀ " => ZFClass.sInter
open scoped ZFSet in
open scoped ZFSet in

lemma cmem_sInter (h : A.Nonempty) : B ᶜ∈ ⋂₀ A ↔ ∀ z, z ᶜ∈ A → B ᶜ∈ z := by
  constructor
  · intro hB z hz
    exact cmem_of_cmem_sInter hB hz
  · intro H
    obtain ⟨z, hz⟩ := h
    obtain ⟨x, rfl, -⟩ := H z (coe_cmem.2 hz)
    refine ⟨x, rfl, ?_⟩
    show x ∈ ⋂₀ A
    rw [mem_sInter]
    intro w hw
    obtain ⟨x', hx', hxw⟩ := H w (coe_cmem.2 hw)
    have hxx : x' = x := by
      apply ZFSet.ext
      intro y
      have := congrArg (fun C : ZFClass.{u} => y ∈ C) hx'
      exact (Iff.of_eq this :)
    subst hxx
    exact hxw
