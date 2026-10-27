/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFClass.cmem_sInter
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 139
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
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
    obtain ⟨w, hw_eq, hw_mem⟩ := hB
    rw [mem_sInter] at hw_mem
    obtain ⟨x, hx_eq, hx_mem⟩ := hz
    have hwx : w ∈ x := hw_mem x hx_mem
    have hw_z : w ᶜ∈ z := by
      rw [← hx_eq]
      exact coe_cmem.2 hwx
    rw [← hw_eq]
    exact hw_z
  · intro H
    obtain ⟨a, ha⟩ := h
    have ha_cmem : (a : ZFClass) ᶜ∈ A := coe_cmem.2 ha
    obtain ⟨x, hx_eq, hx_mem⟩ := H (a : ZFClass) ha_cmem
    have hx_sInter : x ∈ ⋂₀ A := by
      rw [mem_sInter]
      intro y hy
      have hy_cmem : (y : ZFClass) ᶜ∈ A := coe_cmem.2 hy
      obtain ⟨w, hw_eq, hw_mem⟩ := H (y : ZFClass) hy_cmem
      have hxw : x = w := by
        apply SetLike.coe_injective
        rw [hx_eq, hw_eq]
      rw [hxw]
      exact hw_mem
    exact ⟨x, hx_eq, hx_sInter⟩
