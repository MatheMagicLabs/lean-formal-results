/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFClass.cmem_sInter
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 139
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  LS1-leanstral-loop, arm L3, verified in round 2 (round 0 = first attempt)
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 in a fixed check-and-repair loop: L1 = 1 candidate per round, L3 = up to 3
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
    exact ZFClass.cmem_of_cmem_sInter hB hz
  · intro h_all
    rcases h with ⟨z0, hz0⟩
    have hz0_cmem : z0 ᶜ∈ A := ⟨z0, rfl, hz0⟩
    rcases h_all z0 hz0_cmem with ⟨x, hx_eq, hx_mem⟩
    refine ⟨x, hx_eq, ?_⟩
    rw [ZFClass.mem_sInter]
    intro z hz
    have hz_cmem : z ᶜ∈ A := ⟨z, rfl, hz⟩
    rcases h_all z hz_cmem with ⟨y, hy_eq, hy_mem⟩
    have hxy : x = y := SetLike.coe_injective (hx_eq.trans hy_eq.symm)
    rw [hxy]
    exact hy_mem
