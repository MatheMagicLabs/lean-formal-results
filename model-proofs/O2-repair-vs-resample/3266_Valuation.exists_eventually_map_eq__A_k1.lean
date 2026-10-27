/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.exists_eventually_map_eq
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 222
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem exists_eventually_map_eq {x₀ : Completion K} (hx₀ : x₀ ≠ 0) :
    ∃ z₀ : K, z₀ ≠ 0 ∧ ∀ᶠ x in Filter.comap ((↑) : K → Completion K) (𝓝 x₀), v x = v z₀ := by
  obtain ⟨V, V_in, hV⟩ : ∃ V ∈ 𝓝 (1 : Completion K),
      ∀ x : K, (x : Completion K) ∈ V → v x = 1 := by
    have h1 : {x : K | v x = 1} ∈ 𝓝 (1 : K) := by
      filter_upwards [v.locally_const (show v (1 : K) ≠ 0 by simp)] with y hy
      simpa using hy
    rw [Completion.isDenseInducing_coe.nhds_eq_comap, mem_comap, Completion.coe_one] at h1
    obtain ⟨V, V_in, hV⟩ := h1
    exact ⟨V, V_in, fun x hx => hV hx⟩
  have hg : Tendsto (fun p : Completion K × Completion K => p.1 * p.2⁻¹)
      (𝓝 (x₀, x₀)) (𝓝 1) := by
    have : ContinuousAt (fun p : Completion K × Completion K => p.1 * p.2⁻¹) (x₀, x₀) :=
      continuous_fst.continuousAt.mul (continuous_snd.continuousAt.inv₀ hx₀)
    simpa [mul_inv_cancel₀ hx₀] using this.tendsto
  have hU : (fun p : Completion K × Completion K => p.1 * p.2⁻¹) ⁻¹' V ∈ 𝓝 x₀ ×ˢ 𝓝 x₀ := by
    rw [← nhds_prod_eq]
    exact hg V_in
  obtain ⟨U, U_in, hU'⟩ := Filter.mem_prod_self_iff.mp hU
  obtain ⟨z₀, hz₀U, hz₀0⟩ :=
    Completion.denseRange_coe.mem_nhds (inter_mem U_in (compl_singleton_mem_nhds hx₀))
  have z₀_ne : z₀ ≠ 0 := by
    rintro rfl
    exact hz₀0 (by simp)
  refine ⟨z₀, z₀_ne, ?_⟩
  refine Filter.mem_comap.mpr ⟨U, U_in, fun x (hx : (x : Completion K) ∈ U) => ?_⟩
  have h1 : v (x * z₀⁻¹) = 1 := by
    apply hV
    have hinv : ((z₀⁻¹ : K) : Completion K) = (z₀ : Completion K)⁻¹ :=
      map_inv₀ (Completion.coeRingHom : K →+* Completion K) z₀
    rw [Completion.coe_mul, hinv]
    exact hU' (mk_mem_prod hx hz₀U)
  show v x = v z₀
  calc v x = v (x * z₀⁻¹ * z₀) := by rw [mul_assoc, inv_mul_cancel₀ z₀_ne, mul_one]
    _ = v (x * z₀⁻¹) * v z₀ := v.map_mul _ _
    _ = v z₀ := by rw [h1, one_mul]
