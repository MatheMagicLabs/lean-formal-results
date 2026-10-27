/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Complex.hasDerivAt_Gamma_of_re_pos
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean, line 65
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Filter Set Real Asymptotics
open scoped Topology
namespace Complex
section GammaHasDeriv

theorem hasDerivAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt Gamma (∫ t : ℝ in Ioi 0, t ^ (s - 1) * (Real.log t * Real.exp (-t))) s := by
  refine (hasDerivAt_GammaIntegral hs).congr_of_eventuallyEq ?_
  filter_upwards [(continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs] with t ht
  exact Gamma_eq_integral ht
