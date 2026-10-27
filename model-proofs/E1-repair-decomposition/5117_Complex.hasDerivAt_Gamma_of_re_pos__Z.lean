/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Complex.hasDerivAt_Gamma_of_re_pos
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean, line 65
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm Z, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Filter Set Real Asymptotics
open scoped Topology
namespace Complex
section GammaHasDeriv

theorem hasDerivAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt Gamma (∫ t : ℝ in Ioi 0, t ^ (s - 1) * (Real.log t * Real.exp (-t))) s := by
  have h := hasDerivAt_GammaIntegral hs
  apply h.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
  solve
  | apply Gamma_eq_GammaIntegral <;> assumption
  | symm
    apply Gamma_eq_GammaIntegral <;> assumption
  | apply GammaIntegral_eq_Gamma <;> assumption
  | symm
    apply GammaIntegral_eq_Gamma <;> assumption
  | apply Gamma_eq_integral <;> assumption
  | symm
    apply Gamma_eq_integral <;> assumption
