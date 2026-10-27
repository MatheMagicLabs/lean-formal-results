/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     isNormableSpace_of_finiteDimensional
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/Module/FiniteDimension.lean, line 614
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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

theorem isNormableSpace_of_finiteDimensional [FiniteDimensional 𝕜 E] : IsNormableSpace 𝕜 E := by
  let f : E →ₗ[𝕜] SeparationQuotient E :=
    { toFun := SeparationQuotient.mk
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  letI : IsNormableSpace 𝕜 (SeparationQuotient E) :=
    isNormableSpace_of_t2Space_finiteDimensional
      (𝕜 := 𝕜) (E := SeparationQuotient E)
  exact Topology.IsInducing.isNormableSpace
    (f := f) SeparationQuotient.isInducing_mk
