/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.VectorMeasure.integral_continuousLinearMap_comp
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/SetIntegral.lean, line 386
             (added after the model's training data; human proof 25 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 3 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem integral_continuousLinearMap_comp
    {f : X → H} {C : H →L[ℝ] E} (hf : Integrable f μ.variation) :
    ∫ᵛ y, C (f y) ∂[B; μ] = ∫ᵛ y, f y ∂[B ∘L C; μ] := by
  by_cases hG : CompleteSpace G
  swap
  · simp [integral_of_not_completeSpace hG]
  letI := hG
  have hcont : Continuous (fun u : X →₁[μ.variation] H => ∫ᵛ x, C (u x) ∂[B; μ]) := (continuous_integral.comp (C.compLpL 1 μ.variation).continuous).congr (fun u => integral_congr_ae (C.coeFn_compLp u))
  apply hf.induction (P := fun f => ∫ᵛ y, C (f y) ∂[B; μ] = ∫ᵛ y, f y ∂[B ∘L C; μ])
  · intro c s hs hc; haveI : IsFiniteMeasure (μ.variation.restrict s) := ⟨by simpa⟩; have heq : (fun x => C (s.indicator (fun _ => c) x)) = s.indicator (fun _ => C c) := (by funext x; by_cases hx : x ∈ s <;> simp [hx]); rw [heq, integral_indicator_const _ hs, integral_indicator_const _ hs]; rfl
  · intro f g _ hf hg h'f h'g; simp only [Pi.add_apply, C.map_add]; rw [integral_fun_add (C.integrable_comp hf) (C.integrable_comp hg), integral_fun_add hf hg, h'f, h'g]
  · exact isClosed_eq hcont continuous_integral
  · intro f g hfg _ h; have hC : (fun x => C (f x)) =ᵐ[μ.variation] (fun x => C (g x)) := hfg.mono (fun x hx => congrArg C hx); exact (integral_congr_ae (B := B) hC).symm.trans (h.trans (integral_congr_ae (B := B ∘L C) hfg))
