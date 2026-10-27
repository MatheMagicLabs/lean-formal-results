/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.hasDerivAt_Gamma_of_pos
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean, line 155
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Filter Set Real Asymptotics
open scoped Topology
namespace Complex
section GammaHasDeriv
end GammaHasDeriv
end Complex
namespace Real
open Complex MeasureTheory

theorem hasDerivAt_Gamma_of_pos {s : ℝ} (hs : 0 < s) :
    HasDerivAt Gamma (∫ t in Ioi 0, t ^ (s - 1) * (log t * exp (-t))) s := by
  have hs' : 0 < (s : ℂ).re := by simpa using hs
  have h1 := Complex.hasDerivAt_GammaIntegral hs'
  have h2 := h1.congr_of_eventuallyEq (f₁ := Complex.Gamma) (by
    filter_upwards [(Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs']
      with z hz using Complex.Gamma_eq_integral hz)
  have h3 := h2.real_of_complex
  have e : Real.Gamma = fun x : ℝ => (Complex.Gamma (x : ℂ)).re := by
    funext x
    rw [Complex.Gamma_ofReal, Complex.ofReal_re]
  rw [e]
  convert h3 using 1
  have key : (∫ t : ℝ in Ioi 0, ((t ^ (s - 1) * (Real.log t * Real.exp (-t)) : ℝ) : ℂ))
      = ((∫ t : ℝ in Ioi 0, t ^ (s - 1) * (Real.log t * Real.exp (-t)) : ℝ) : ℂ) :=
    integral_ofReal
  rw [← Complex.ofReal_re (∫ t : ℝ in Ioi 0, t ^ (s - 1) * (Real.log t * Real.exp (-t))),
    ← key]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht' : (0:ℝ) < t := ht
  simp only [Complex.ofReal_mul, Complex.ofReal_cpow ht'.le, Complex.ofReal_sub,
    Complex.ofReal_one]
