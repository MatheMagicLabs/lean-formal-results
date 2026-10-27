/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.HasLimitProcess.congr
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 59
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open MeasureTheory Filter
open scoped Topology ENNReal NNReal
namespace MeasureTheory.Filtration
variable {ι Ω E F G : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
section HasLimitProcess

lemma HasLimitProcess.congr (h : X ≡ᵐ[P] Y) (hX : HasLimitProcess X 𝓕 P) :
    HasLimitProcess Y 𝓕 P := by
  obtain ⟨Z, hZm, hZ⟩ := hX
  refine ⟨Z, hZm, ?_⟩
  filter_upwards [hZ, h.ae_eq] with ω h1 h2
  have h3 : (fun i => Y i ω) = fun i => X i ω := funext fun i => (congrFun h2 i).symm
  rw [h3]
  exact h1
