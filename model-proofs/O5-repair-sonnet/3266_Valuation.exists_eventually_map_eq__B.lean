/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.exists_eventually_map_eq
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 222
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 2 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem exists_eventually_map_eq {x₀ : Completion K} (hx₀ : x₀ ≠ 0) :
    ∃ z₀ : K, z₀ ≠ 0 ∧ ∀ᶠ x in Filter.comap ((↑) : K → Completion K) (𝓝 x₀), v x = v z₀ := by
  have hv1 : ∀ᶠ x in 𝓝 (1 : K), v x = 1 := by
    have h := v.locally_const (x := (1 : K)) (by simp)
    filter_upwards [h] with x hx
    simpa using hx
  have hV : {y : K | v y = 1} ∈ Filter.comap ((↑) : K → Completion K) (𝓝 (1 : Completion K)) := by
    have h := Completion.isDenseInducing_coe.nhds_eq_comap (1 : K)
    rw [Completion.coe_one] at h
    rw [← h]
    exact hv1
  obtain ⟨V, V_in, hVsub⟩ := Filter.mem_comap.1 hV
  have hcont : ContinuousAt (fun p : Completion K × Completion K => p.1 * p.2⁻¹) (x₀, x₀) :=
    continuous_fst.continuousAt.mul (continuous_snd.continuousAt.inv₀ hx₀)
  have hW := hcont.preimage_mem_nhds (t := V) (by
    show V ∈ 𝓝 (x₀ * x₀⁻¹)
    rw [mul_inv_cancel₀ hx₀]
    exact V_in)
  obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := mem_nhds_prod_iff.1 hW
  haveI := Completion.isDenseInducing_coe.comap_nhds_neBot x₀
  have hz : ∀ᶠ z : K in Filter.comap ((↑) : K → Completion K) (𝓝 x₀),
      (z : Completion K) ∈ U₂ ∧ (z : Completion K) ≠ 0 := by
    have h1 : ∀ᶠ z : K in Filter.comap ((↑) : K → Completion K) (𝓝 x₀), (z : Completion K) ∈ U₂ :=
      Filter.tendsto_comap.eventually (p := fun y => y ∈ U₂) hU₂
    have h2 : ∀ᶠ z : K in Filter.comap ((↑) : K → Completion K) (𝓝 x₀), (z : Completion K) ≠ 0 :=
      Filter.tendsto_comap.eventually (eventually_ne_nhds hx₀)
    exact h1.and h2
  obtain ⟨z₀, hz₀U, hz₀ne⟩ := hz.exists
  have hz0 : z₀ ≠ 0 := fun h => hz₀ne (by rw [h, Completion.coe_zero])
  refine ⟨z₀, hz0, ?_⟩
  have h3 : ∀ᶠ x : K in Filter.comap ((↑) : K → Completion K) (𝓝 x₀), (x : Completion K) ∈ U₁ :=
    Filter.tendsto_comap.eventually (p := fun y => y ∈ U₁) hU₁
  filter_upwards [h3] with x hx
  have hmem : ((x : Completion K), (z₀ : Completion K)) ∈ U₁ ×ˢ U₂ := ⟨hx, hz₀U⟩
  have this : (x : Completion K) * (z₀ : Completion K)⁻¹ ∈ V := hsub hmem
  have e : ((x * z₀⁻¹ : K) : Completion K) = (x : Completion K) * (z₀ : Completion K)⁻¹ := by
    have h := map_mul (Completion.coeRingHom : K →+* Completion K) x z₀⁻¹
    rw [map_inv₀] at h
    exact h
  have h1 : v (x * z₀⁻¹) = 1 := hVsub (by rw [Set.mem_preimage, e]; exact this)
  rw [map_mul, map_inv₀] at h1
  exact (mul_inv_eq_one₀ ((v.ne_zero_iff).2 hz0)).1 h1
