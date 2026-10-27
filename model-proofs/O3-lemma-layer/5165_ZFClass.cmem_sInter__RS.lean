/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFClass.cmem_sInter
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 139
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  refine ⟨fun hy z hz => cmem_of_cmem_sInter hy hz, fun H => ?_⟩
  obtain ⟨z, hz⟩ := h
  obtain ⟨y, rfl, -⟩ := H z (coe_cmem.2 hz)
  rw [coe_cmem, mem_sInter]
  intro w hw
  simpa using coe_cmem.1 (H w (coe_cmem.2 hw))
