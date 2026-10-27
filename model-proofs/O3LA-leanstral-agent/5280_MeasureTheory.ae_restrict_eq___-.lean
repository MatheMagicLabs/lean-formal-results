/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.ae_restrict_eq₀
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/Restrict.lean, line 697
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open scoped ENNReal NNReal Topology
open Set MeasureTheory Measure Filter MeasurableSpace ENNReal Function
variable {R α β δ ι : Type*}
namespace MeasureTheory
variable {m0 : MeasurableSpace α} [MeasurableSpace β]
variable {μ ν : Measure α} {s s' t : Set α}
namespace Measure
set_option backward.isDefEq.respectTransparency false in
variable (μ)
variable {μ}
end Measure
open scoped Interval in
open scoped Interval in
open scoped Interval in

theorem ae_restrict_eq₀ (hs : NullMeasurableSet s μ) : ae (μ.restrict s) = ae μ ⊓ 𝓟 s := by
  ext t
  simp only [mem_ae_iff, mem_inf_principal, restrict_apply₀' hs]
  have h : (tᶜ ∩ s) = {x | x ∈ s → x ∈ t}ᶜ := by
    ext x; simp [and_comm]
  simp [h]
