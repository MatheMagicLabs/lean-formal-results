/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     isNormableSpace_of_t2Space_finiteDimensional
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/Module/FiniteDimension.lean, line 605
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Filter Module Set TopologicalSpace Topology
universe u v w x
noncomputable section
section FiniteDimensional
variable {𝕜 E F : Type*}
end FiniteDimensional
section NormedField
variable {𝕜 : Type u} [hnorm : NontriviallyNormedField 𝕜] {E : Type v} [AddCommGroup E] [Module 𝕜 E]
variable [CompleteSpace 𝕜]
namespace LinearMap
variable [T2Space E] [FiniteDimensional 𝕜 E]
end LinearMap
section
variable [T2Space E] [T2Space F] [FiniteDimensional 𝕜 E]
namespace LinearEquiv
end LinearEquiv
variable [FiniteDimensional 𝕜 F]
end
namespace Module.Basis
variable {ι : Type*} [Finite ι] [T2Space E]
end Module.Basis
namespace ContinuousLinearMap
variable [T2Space E] [FiniteDimensional 𝕜 E]
end ContinuousLinearMap
end NormedField
section IsUniformAddGroup
variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
variable {𝕜 E}
end IsUniformAddGroup
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable (E) in

private lemma isNormableSpace_of_t2Space_finiteDimensional
    [T2Space E] [FiniteDimensional 𝕜 E] : IsNormableSpace 𝕜 E := by
  let e := (Module.finBasis 𝕜 E).equivFunL
  first
  | exact e.isNormableSpace
  | exact e.symm.isNormableSpace
  | exact e.isNormableSpace_iff.mpr inferInstance
  | exact e.symm.isNormableSpace_iff.mp inferInstance
  | exact IsNormableSpace.of_continuousLinearEquiv e
  | exact IsNormableSpace.of_continuousLinearEquiv e.symm
