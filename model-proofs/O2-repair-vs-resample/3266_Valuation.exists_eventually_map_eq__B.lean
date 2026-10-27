/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.exists_eventually_map_eq
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 222
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem exists_eventually_map_eq {x₀ : Completion K} (hx₀ : x₀ ≠ 0) :
    ∃ z₀ : K, z₀ ≠ 0 ∧ ∀ᶠ x in Filter.comap ((↑) : K → Completion K) (𝓝 x₀), v x = v z₀ := by
  have h1 : v (1 : K) ≠ 0 := by simp
  have hK : ∀ᶠ y in 𝓝 (1 : K), v y = v 1 := v.locally_const h1
  rw [Completion.isDenseInducing_coe.nhds_eq_comap, Filter.eventually_comap,
    Completion.coe_one] at hK
  have hc : ContinuousAt (fun p : Completion K × Completion K ↦ p.1 * p.2⁻¹) (x₀, x₀) :=
    continuous_fst.continuousAt.mul (continuous_snd.continuousAt.inv₀ hx₀)
  have ht : Tendsto (fun p : Completion K × Completion K ↦ p.1 * p.2⁻¹)
      (𝓝 (x₀, x₀)) (𝓝 1) := by
    simpa [mul_inv_cancel₀ hx₀] using hc.tendsto
  have h2 := ht.eventually hK
  obtain ⟨u, hu, w, hw, huw⟩ := mem_nhds_prod_iff.1 h2
  have hUmem : u ∩ w ∩ ({0}ᶜ : Set (Completion K)) ∈ 𝓝 x₀ :=
    inter_mem (inter_mem hu hw) (compl_singleton_mem_nhds hx₀)
  obtain ⟨z₀, hz₀⟩ := Completion.denseRange_coe.mem_nhds hUmem
  have hz0 : z₀ ≠ 0 := fun h ↦ hz₀.2 (by simp [h])
  refine ⟨z₀, hz0, ?_⟩
  filter_upwards [preimage_mem_comap hUmem] with x hx
  have this : ∀ a : K, (a : Completion K) = (x : Completion K) * (z₀ : Completion K)⁻¹ →
      v a = v 1 :=
    huw (show ((x : Completion K), (z₀ : Completion K)) ∈ u ×ˢ w from ⟨hx.1.1, hz₀.1.2⟩)
  have h3 : v (x * z₀⁻¹) = v 1 := by
    refine this (x * z₀⁻¹) ?_
    rw [Completion.coe_mul, Completion.coe_inv]
  rw [map_mul, map_inv₀, map_one] at h3
  exact (mul_inv_eq_one₀ ((Valuation.ne_zero_iff v).2 hz0)).1 h3
