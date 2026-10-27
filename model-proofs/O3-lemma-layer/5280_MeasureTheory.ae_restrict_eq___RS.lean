/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.ae_restrict_eq₀
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/Restrict.lean, line 697
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  refine le_antisymm (le_inf ae_restrict_le (le_principal_iff.2 (ae_restrict_mem₀ hs))) le_ae_restrict
