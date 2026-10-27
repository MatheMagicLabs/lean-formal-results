/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Complex.hasDerivAt_Gamma_of_re_pos
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean, line 65
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Filter Set Real Asymptotics
open scoped Topology
namespace Complex
section GammaHasDeriv

theorem hasDerivAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt Gamma (∫ t : ℝ in Ioi 0, t ^ (s - 1) * (Real.log t * Real.exp (-t))) s := by
  apply (hasDerivAt_GammaIntegral hs).congr_of_eventuallyEq
  have hpos : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re :=
    (isOpen_lt continuous_const continuous_re).mem_nhds hs
  filter_upwards [hpos] with z hz
  exact Gamma_eq_integral hz
