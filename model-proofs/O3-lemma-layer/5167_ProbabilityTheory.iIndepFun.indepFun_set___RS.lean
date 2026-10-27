/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ProbabilityTheory.iIndepFun.indepFun_set₀
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Independence/Process/Basic.lean, line 442
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  exact Kernel.iIndepFun.indepFun_set₀ (κ := Kernel.const Unit P) (P := Measure.dirac ())
    hIJ hX (fun s => by simpa using mX s)
