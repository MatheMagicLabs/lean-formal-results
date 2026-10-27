/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ContinuousLinearMap.exists_eq_flip_toLinearMap
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Operator/Bilinear.lean, line 175
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 3 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private lemma exists_eq_flip_toLinearMap (f : E' →SL[σ₁₃] F' →SL[σ₂₃] G') :
    ∃ g : F' →SL[σ₂₃] E' →SL[σ₁₃] G', ∀ a b, f.toLinearMap₁₂.flip a b = g a b := by
  obtain ⟨p, hp⟩ := (‹IsNormableSpace 𝕜₂ F'›).1
  obtain ⟨q, hq⟩ := (‹IsNormableSpace 𝕜₃ G'›).1
  haveI : IsTopologicalAddGroup F' := by
    first
      | exact hp.topologicalAddGroup
      | exact hp.isTopologicalAddGroup
      | infer_instance
  let L : F' →ₛₗ[σ₂₃] (E' →SL[σ₁₃] G') :=
    { toFun := fun b =>
        { toFun := fun a => f a b
          map_add' := fun x y => by simp
          map_smul' := fun c x => by simp
          cont := (continuous_eval_const b).comp f.continuous }
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp }
  refine ⟨⟨L, ?_⟩, fun a b => rfl⟩
  refine continuous_of_continuousAt_zero L ?_
  unfold ContinuousAt
  rw [map_zero, ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff]
  rintro ⟨S, V⟩ ⟨hS, hV⟩
  dsimp only at hS hV ⊢
  obtain ⟨Q, δ, hδ, hball, hV1⟩ : ∃ (Q : Seminorm 𝕜₃ G') (δ : ℝ), 0 < δ ∧
      Q.ball 0 δ ⊆ V ∧ Q.ball 0 1 ∈ 𝓝 (0 : G') := by
    obtain ⟨i, hi, hb⟩ := (hq.hasBasis_ball (x := (0 : G'))).mem_iff.1 hV
    exact ⟨_, i.2, hi, hb, (hq.hasBasis_ball (x := (0 : G'))).mem_of_mem (i := (i.1, 1)) one_pos⟩
  have hT : Bornology.IsVonNBounded 𝕜₂ {y : F' | p y < 1} :=
    hp.isVonNBounded_iff_seminorm_bounded.2 fun _ => ⟨1, one_pos, fun x hx => hx⟩
  have hmem : {g : F' →SL[σ₂₃] G' | ∀ y ∈ {y : F' | p y < 1}, g y ∈ Q.ball 0 1} ∈
      𝓝 (0 : F' →SL[σ₂₃] G') :=
    ContinuousLinearMap.hasBasis_nhds_zero.mem_of_mem
      (i := ({y : F' | p y < 1}, Q.ball 0 1)) ⟨hT, hV1⟩
  have hf0 := f.continuous.tendsto 0
  rw [map_zero] at hf0
  have hW := hf0 hmem
  obtain ⟨r, hr, hrc⟩ := (hS hW).exists_pos
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 r
  have hSc := hrc c hc.le
  obtain ⟨k, hkc⟩ := NormedField.exists_lt_norm 𝕜₂ (‖c‖ / δ)
  have hk : 0 < ‖k‖ := lt_of_le_of_lt (div_nonneg (norm_nonneg _) hδ.le) hkc
  have hk0 : k ≠ 0 := norm_pos_iff.1 hk
  have hpc : Continuous p := by
    first
      | exact hp.continuous_seminorm default
      | exact hp.continuous_seminorm 0
      | exact hp.continuous_seminorm ()
  have hU : {y : F' | p y < ‖k‖⁻¹} ∈ 𝓝 (0 : F') := by
    refine IsOpen.mem_nhds (isOpen_lt hpc continuous_const) ?_
    show p 0 < ‖k‖⁻¹
    rw [map_zero]
    positivity
  have hA : ‖σ₁₃ c‖ = ‖c‖ := by
    first
      | exact RingHomIsometric.norm_map
      | exact RingHomIsometric.is_iso
      | simp
  have hB : ‖σ₂₃ k⁻¹‖ = ‖k⁻¹‖ := by
    first
      | exact RingHomIsometric.norm_map
      | exact RingHomIsometric.is_iso
      | simp
  filter_upwards [hU] with y hy
  show ∀ x ∈ S, f x y ∈ V
  intro x hx
  obtain ⟨w, hw, rfl⟩ := Set.mem_smul_set.1 (hSc hx)
  have hw' : ∀ z ∈ {y : F' | p y < 1}, f w z ∈ Q.ball 0 1 := hw
  have hz : p (k • y) < 1 := by
    rw [map_smul_eq_mul]
    calc ‖k‖ * p y < ‖k‖ * ‖k‖⁻¹ := mul_lt_mul_of_pos_left hy hk
      _ = 1 := mul_inv_cancel₀ hk.ne'
  have hQv : Q (f w (k • y)) < 1 := by
    have := hw' (k • y) hz
    rwa [Seminorm.mem_ball_zero] at this
  have h2 : f w y = σ₂₃ k⁻¹ • f w (k • y) := by
    rw [← map_smulₛₗ (f w), smul_smul, inv_mul_cancel₀ hk0, one_smul]
  have h1 : f (c • w) y = σ₁₃ c • f w y := by
    rw [map_smulₛₗ]
    rfl
  apply hball
  rw [Seminorm.mem_ball_zero, h1, h2, map_smul_eq_mul, map_smul_eq_mul, hA, hB, norm_inv]
  have hQ0 : 0 ≤ Q (f w (k • y)) := apply_nonneg _ _
  have hb : 0 < ‖k‖⁻¹ := inv_pos.2 hk
  have hcδ : ‖c‖ < ‖k‖ * δ := (div_lt_iff₀ hδ).1 hkc
  have hlt : ‖c‖ * ‖k‖⁻¹ < δ := by
    rw [← div_eq_mul_inv, div_lt_iff₀ hk]
    linarith
  calc ‖c‖ * (‖k‖⁻¹ * Q (f w (k • y))) ≤ ‖c‖ * ‖k‖⁻¹ :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hb.le hQv.le) (norm_nonneg _)
    _ < δ := hlt
