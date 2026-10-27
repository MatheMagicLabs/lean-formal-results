/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.VectorMeasure.integral_continuousLinearMap_comp
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/SetIntegral.lean, line 386
             (added after the model's training data; human proof 25 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 2 call(s)
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
  · letI := hG
    apply hf.induction (P := fun f ↦
      ∫ᵛ y, C (f y) ∂[B; μ] = ∫ᵛ y, f y ∂[B ∘L C; μ])
    · intro c s hs hc
      have : IsFiniteMeasure (μ.variation.restrict s) := ⟨by simpa⟩
      have hC : (fun y ↦ C (s.indicator (fun _ ↦ c) y)) =
          s.indicator (fun _ ↦ C c) := by
        ext y
        by_cases hy : y ∈ s <;> simp [hy]
      rw [hC]
      simp [integral_indicator_const _ hs]
    · intro f g _ hf hg h₁ h₂
      simp only [Pi.add_apply, ContinuousLinearMap.map_add]
      rw [integral_fun_add (C.integrable_comp hf) (C.integrable_comp hg),
        integral_fun_add hf hg, h₁, h₂]
    · apply isClosed_eq
      · have hcont := (C.compLpL 1 μ.variation).continuous
        convert continuous_integral.comp hcont using 1
        ext u
        apply integral_congr_ae
        first
        | exact (C.coeFn_compLp u).symm
        | exact (ContinuousLinearMap.coeFn_compLp C u).symm
        | exact (C.coeFn_compLpL u).symm
        | exact (C.compLp_coeFn u).symm
      · exact continuous_integral
    · intro f g hfg _ h
      have hC : (fun y ↦ C (f y)) =ᵐ[μ.variation] (fun y ↦ C (g y)) :=
        hfg.mono fun y hy ↦ congrArg C hy
      rw [← integral_congr_ae hC, ← integral_congr_ae hfg, h]
  · first
    | simp only [integral_of_not_completeSpace hG]
    | simp [integral_def, hG]
