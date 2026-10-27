/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.exists_eventually_map_eq
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 222
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem exists_eventually_map_eq {x₀ : Completion K} (hx₀ : x₀ ≠ 0) :
    ∃ z₀ : K, z₀ ≠ 0 ∧ ∀ᶠ x in Filter.comap ((↑) : K → Completion K) (𝓝 x₀), v x = v z₀ := by
  haveI : (Filter.comap ((↑) : K → Completion K) (𝓝 x₀)).NeBot := by
    first
      | exact Completion.isDenseInducing_coe.comap_nhds_neBot x₀
      | infer_instance
  obtain ⟨u, w, hu, hw, h0u, hx₀w, hdisj⟩ := t2_separation (Ne.symm hx₀)
  have hnhds : ∀ a : K, 𝓝 a = Filter.comap ((↑) : K → Completion K) (𝓝 (a : Completion K)) :=
    fun a ↦ Completion.isDenseInducing_coe.nhds_eq_comap a
  have hU : (((↑) : K → Completion K) ⁻¹' u : Set K) ∈ 𝓝 (0 : K) := by
    rw [hnhds 0]
    refine Filter.preimage_mem_comap ?_
    rw [Completion.coe_zero]
    exact hu.mem_nhds h0u
  obtain ⟨γ, hγ⟩ := (v.mem_nhds_zero_iff _).1 hU
  have hB : {x : K | v.restrict x < γ} ∈ 𝓝 (0 : K) :=
    (v.mem_nhds_zero_iff {x : K | v.restrict x < γ}).2 ⟨γ, fun x hx ↦ hx⟩
  rw [hnhds 0, Filter.mem_comap] at hB
  obtain ⟨V0, hV0, hV0B⟩ := hB
  rw [Completion.coe_zero] at hV0
  have hsub : {p : Completion K × Completion K | p.1 - p.2 ∈ V0} ∈ 𝓝 (x₀, x₀) := by
    have h1 : Tendsto (fun p : Completion K × Completion K => p.1 - p.2) (𝓝 (x₀, x₀))
        (𝓝 (x₀ - x₀)) :=
      (continuous_fst.sub continuous_snd).tendsto (x₀, x₀)
    rw [sub_self] at h1
    exact h1 hV0
  obtain ⟨p, hp, q, hq, hpq⟩ := mem_nhds_prod_iff.1 hsub
  have hNmem : p ∩ q ∩ w ∈ 𝓝 x₀ :=
    Filter.inter_mem (Filter.inter_mem hp hq) (hw.mem_nhds hx₀w)
  have hNF : ((↑) : K → Completion K) ⁻¹' (p ∩ q ∩ w) ∈
      Filter.comap ((↑) : K → Completion K) (𝓝 x₀) :=
    Filter.preimage_mem_comap hNmem
  obtain ⟨z₀, hz₀⟩ := Filter.nonempty_of_mem hNF
  have hz₀' : ((z₀ : K) : Completion K) ∈ p ∩ q ∩ w := hz₀
  have hz₀B : ¬ v.restrict z₀ < γ := by
    intro h
    have : ((z₀ : K) : Completion K) ∈ u := hγ h
    exact Set.disjoint_left.1 hdisj this hz₀'.2
  have hz0 : z₀ ≠ 0 := by
    rintro rfl
    apply hz₀B
    first
      | (rw [map_zero]; exact zero_lt_iff.2 γ.ne_zero)
      | simp [zero_lt_iff]
  refine ⟨z₀, hz0, ?_⟩
  filter_upwards [hNF] with x hx
  have hx' : ((x : K) : Completion K) ∈ p ∩ q ∩ w := hx
  have hmem : ((x - z₀ : K) : Completion K) ∈ V0 := by
    rw [Completion.coe_sub]
    exact hpq (Set.mk_mem_prod hx'.1.1 hz₀'.1.2)
  have h1 : v.restrict (x - z₀) < γ := hV0B hmem
  have h2 : (γ : v.ValueGroup₀) ≤ v.restrict z₀ := not_lt.1 hz₀B
  have h3 : v (x - z₀) < v z₀ := v.restrict_lt_iff.1 (lt_of_lt_of_le h1 h2)
  exact Valuation.map_eq_of_sub_lt v h3
