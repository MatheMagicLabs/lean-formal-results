/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.closure_image_coe_ofPred_map_lt
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 346
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Valuation ValuativeRel IsValuativeTopology UniformSpace MonoidWithZeroHom ValueGroup₀
open Set Filter Topology
variable {R K Γ₀ : Type*}
section Ring
namespace IsValuativeTopology
variable [Ring R] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)
open WithZeroTopology
end IsValuativeTopology
end Ring
section DivisionRing
variable [DivisionRing K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
section InversionEstimate
end InversionEstimate
namespace IsValuativeTopology
variable [ValuativeRel K] [TopologicalSpace K] [IsValuativeTopology K]
section WithZeroTopology
variable [v.Compatible]
open WithZeroTopology
end WithZeroTopology
end IsValuativeTopology
end DivisionRing
section Field
variable [Field K] [ValuativeRel K] [UniformSpace K] [IsValuativeTopology K]
namespace IsValuativeTopology
end IsValuativeTopology
namespace Valuation
variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) [v.Compatible]
open WithZeroTopology
variable [IsUniformAddGroup K]

theorem closure_image_coe_ofPred_map_lt {r : Γ₀} (hr : r ≠ 0) :
    closure ((↑) '' {x : K | v x < r}) = {x : Completion K | v.extension x < r} := by
  have hf : Continuous v.extensionFun := by
    first
    | exact v.continuous_extensionFun
    | exact v.extensionFun_continuous
    | unfold Valuation.extensionFun
      fun_prop
  have heq {x y : Completion K}
      (h : v.extensionFun x = v.extensionFun y) :
      v.extension x = v.extension y := by
    change embedding (v.extensionFun x) = embedding (v.extensionFun y)
    rw [h]
  have hzero {x : Completion K} (h : v.extensionFun x = 0) :
      x = 0 := by
    have hz : v.extension x = 0 := by
      change embedding (v.extensionFun x) = 0
      rw [h, map_zero]
    simpa using hz
  have hopen (x : Completion K) (hx : x ≠ 0) :
      IsOpen {y : Completion K | v.extensionFun y = v.extensionFun x} := by
    have hn : v.extensionFun x ≠ 0 := fun h => hx (hzero h)
    have ho : IsOpen ({v.extensionFun x} : Set _) := by
      first
      | exact WithZeroTopology.isOpen_singleton _ hn
      | exact WithZeroTopology.isOpen_singleton (Units.mk0 _ hn)
      | simpa [WithZeroTopology.isOpen_iff, hn, Ne.symm hn]
      | simpa [IsOpen, WithZeroTopology.topologicalSpace, hn, Ne.symm hn]
      | change (0 ∈ ({v.extensionFun x} : Set _) → _)
        intro h
        exact (hn (mem_singleton_iff.mp h).symm).elim
    exact ho.preimage hf
  have hclosed : IsClosed {x : Completion K | v.extension x < r} := by
    apply isOpen_compl_iff.mp
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      simpa [pos_iff_ne_zero, hr] using hx
    apply Filter.mem_of_superset
      ((hopen x hx0).mem_nhds (show v.extensionFun x = v.extensionFun x from rfl))
    intro y hy
    change ¬v.extension y < r
    change ¬v.extension x < r at hx
    rwa [heq hy]
  apply subset_antisymm
  · apply closure_minimal _ hclosed
    rintro _ ⟨a, ha, rfl⟩
    simpa using ha
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      apply subset_closure
      refine ⟨0, ?_, by simp⟩
      simpa [pos_iff_ne_zero] using hr
    · have hd :
          x ∈ closure (range (fun a : K => (a : Completion K))) := by
        refine Completion.induction_on x isClosed_closure ?_
        intro a
        exact subset_closure ⟨a, rfl⟩
      rw [mem_closure_iff]
      intro U hU hxU
      obtain ⟨y, ⟨hyU, hyf⟩, a, rfl⟩ :=
        mem_closure_iff.mp hd
          (U ∩ {y : Completion K | v.extensionFun y = v.extensionFun x})
          (hU.inter (hopen x hx0)) ⟨hxU, rfl⟩
      refine ⟨(a : Completion K), hyU, a, ?_, rfl⟩
      have ha : v.extension (a : Completion K) < r := by
        rwa [heq hyf]
      simpa using ha
