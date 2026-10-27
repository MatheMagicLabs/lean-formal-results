/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     isImmersionOfComplement_subtypeVal_Icc
Source:      Mathlib @ d0a050ad6, Mathlib/Geometry/Manifold/Instances/Icc.lean, line 72
             (added after the model's training data; human proof 31 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 3 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma isImmersionOfComplement_subtypeVal_Icc :
    IsImmersionOfComplement Unit (𝓡∂ 1) 𝓘(ℝ) n (fun (z : Icc x y) ↦ (z : ℝ)) := by
  intro z
  let φ₀ := ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin 1)) Unit
  let φ := φ₀.trans (PiLp.equivOfUnique 2 ℝ (fun (_ : Fin 1) ↦ ℝ))
  by_cases hz : ↑z < y
  · apply IsImmersionAtOfComplement.mk_of_continuousAt (by fun_prop) φ (chartAt (EuclideanHalfSpace 1) z) (Homeomorph.addLeft (-x)).toOpenPartialHomeomorph (mem_chart_source _ z) (by simp [Homeomorph.addLeft]) (chart_mem_maximalAtlas _) (by { apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn; exact (by { have : ContDiff ℝ n (fun y ↦ -x + y) := (by fun_prop); simpa [contMDiffOn_iff_contDiffOn, contDiffOn_univ] }); exact (by { have : ContDiff ℝ n (fun y ↦ x + y) := (by fun_prop); simpa [contMDiffOn_iff_contDiffOn, contDiffOn_univ, Homeomorph.addLeft] }) }); intro z' hz'; obtain ⟨⟨u, rfl⟩, hu⟩ : (∃ v, ⇑(𝓡∂ 1) v = z') ∧ ⇑(𝓡∂ 1).symm z' ∈ (IccLeftChart x y).target := (by simpa [hz] using! hz'); replace hu : ofLp u.val 0 ≤ y - x := (by { apply le_of_lt; simpa [modelWithCornersEuclideanHalfSpace_symm_apply, max_eq_left u.property] using! hu }); simp [hz, φ, φ₀, modelWithCornersEuclideanHalfSpace_symm_apply, u.property, IccLeftChart_symm_apply_of_le hu]
  · apply IsImmersionAtOfComplement.mk_of_continuousAt (by fun_prop) φ (chartAt (EuclideanHalfSpace 1) z) (Homeomorph.pointReflection (y / 2)).toOpenPartialHomeomorph (mem_chart_source _ z) (by simp [Homeomorph.pointReflection]) (chart_mem_maximalAtlas _) (by { apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn; exact (by { have : ContDiff ℝ n ((fun v ↦ v + y / 2) ∘ fun x ↦ y / 2 - x) := (by fun_prop); simpa [contMDiffOn_iff_contDiffOn, contDiffOn_univ] }); exact (by { have : ContDiff ℝ n ((fun v ↦ -v + y / 2) ∘ fun p' ↦ p' - y / 2) := (by fun_prop); simpa [contMDiffOn_iff_contDiffOn, contDiffOn_univ] }) }); intro z' hz'; obtain ⟨⟨u, rfl⟩, hu⟩ : (∃ v, ⇑(𝓡∂ 1) v = z') ∧ ⇑(𝓡∂ 1).symm z' ∈ (IccRightChart x y).target := (by simpa [hz] using! hz'); replace hu : ofLp u.val 0 ≤ y - x := (by { apply le_of_lt; simpa [modelWithCornersEuclideanHalfSpace_symm_apply, max_eq_left u.property] using! hu }); simp [hz, φ, φ₀, modelWithCornersEuclideanHalfSpace_symm_apply, u.property, IccRightChart_symm_apply_of_le hu, Equiv.pointReflection_apply]; linarith
