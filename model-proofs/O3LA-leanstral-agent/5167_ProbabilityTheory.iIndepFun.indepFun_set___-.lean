/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ProbabilityTheory.iIndepFun.indepFun_set₀
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Independence/Process/Basic.lean, line 442
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open MeasureTheory MeasurableSpace Set
namespace ProbabilityTheory
variable {S T Ω : Type*} {mΩ : MeasurableSpace Ω}
namespace Kernel
variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α Ω} {P : Measure α}
end Kernel
variable {P : Measure Ω}

theorem iIndepFun.indepFun_set₀ {𝓧 : S → Type*} [∀ s, MeasurableSpace (𝓧 s)]
    {X : (s : S) → Ω → 𝓧 s} {I J : Set S} (hIJ : Disjoint I J) (hX : iIndepFun X P)
    (mX : ∀ s, AEMeasurable (X s) P) :
    (fun ω (i : I) ↦ X i ω) ⟂ᵢ[P] (fun ω (j : J) ↦ X j ω) := by
  have h : (fun ω (i : I) ↦ (mX i).mk (X i) ω) ⟂ᵢ[P] (fun ω (j : J) ↦ (mX j).mk (X j) ω) := by
    refine iIndepFun.indepFun_set I J hIJ ?_ fun i ↦ (mX i).measurable_mk
    exact iIndepFun.congr (fun i ↦ (mX i).ae_eq_mk) hX
  refine IndepFun.process_congr h ?_ ?_
  · exact fun i ↦ (mX i).ae_eq_mk.symm
  · exact fun j ↦ (mX j).ae_eq_mk.symm
