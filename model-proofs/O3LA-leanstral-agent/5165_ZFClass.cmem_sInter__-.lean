/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFClass.cmem_sInter
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 139
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
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
  · exact fun hB z hz => cmem_of_cmem_sInter hB hz
  · intro h_all
    obtain ⟨w, hw⟩ := h
    have hBw : B ᶜ∈ (w : ZFClass) := h_all (w : ZFClass) (coe_cmem.2 hw)
    obtain ⟨x, hx, hxw⟩ := hBw
    refine ⟨x, hx, ?_⟩
    rw [mem_sInter]
    intro z hz
    have hBz : B ᶜ∈ (z : ZFClass) := h_all (z : ZFClass) (coe_cmem.2 hz)
    obtain ⟨w', hw', hw'z⟩ := hBz
    have h_coe : (x : ZFClass) = (w' : ZFClass) := by rw [hx, hw']
    have hx_eq_w' : x = w' := SetLike.coe_injective (by rw [hx, hw'])
    rw [hx_eq_w']
    exact hw'z
