/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ContinuousLinearMap.exists_eq_smulRightLₗ
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Operator/Bilinear.lean, line 494
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

suppress_compilation
open Filter hiding map_smul
open scoped NNReal Topology Uniformity
variable {𝕜 𝕜₂ 𝕜₃ E Eₗ E' Eₗ' F Fₗ F' Fₗ' G Gₗ G' Gₗ' : Type*}
section SemiNormed
open ContinuousLinearMap
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup Eₗ] [SeminormedAddCommGroup F]
variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
variable
namespace ContinuousLinearMap
section OpNorm
open Real
variable [RingHomIsometric σ₂₃]
open scoped ENNReal
end OpNorm
end ContinuousLinearMap
namespace LinearMap
variable [RingHomIsometric σ₂₃]
end LinearMap
namespace ContinuousLinearMap
variable [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]
variable (E F G σ₁₃ σ₂₃)
variable {E F G σ₁₃ σ₂₃}
variable (𝕜 E Fₗ Gₗ)
variable {𝕜 E Fₗ Gₗ}
variable (F' σ₁₂)
variable [RingHomIsometric σ₁₂] [IsTopologicalAddGroup F'] [IsTopologicalAddGroup Fₗ']
variable {F' σ₁₂}
variable (𝕜 Fₗ')
variable {𝕜 Fₗ'}
variable (σ₁₂ σ₂₃ E F G E' F' G')
variable {σ₁₂ σ₂₃ E F G E' F' G'}
variable (𝕜 σ₁₂ σ₂₃ E E' Fₗ Fₗ' Gₗ Gₗ')
variable (Eₗ Eₗ') {𝕜 E E' Fₗ Fₗ' Gₗ Gₗ'}
variable [IsTopologicalAddGroup E']
end ContinuousLinearMap
namespace ContinuousLinearMap
variable {E'' F'' : Type*} [AddCommGroup E''] [AddCommGroup F'']
variable {𝕜₁' : Type*} {𝕜₂' : Type*} [NontriviallyNormedField 𝕜₁'] [NontriviallyNormedField 𝕜₂']
variable [RingHomIsometric σ₁₃] [RingHomIsometric σ₁'] [RingHomIsometric σ₂'] [IsNormableSpace 𝕜 E']
variable [IsTopologicalAddGroup Fₗ']
variable (𝕜 E' Fₗ')

private lemma exists_eq_smulRightLₗ :
    ∃ g : StrongDual 𝕜 E' →L[𝕜] Fₗ' →L[𝕜] E' →L[𝕜] Fₗ',
      ∀ a b, smulRightLₗ 𝕜 E' Fₗ' a b = g a b := by
  have key : ∀ (K : Set 𝕜), Bornology.IsBounded K → ∀ U ∈ 𝓝 (0 : Fₗ'),
      ∀ᶠ b in 𝓝 (0 : Fₗ'), ∀ k ∈ K, k • b ∈ U := by
    intro K hK U hU
    obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.1 hK
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 (max r 0)
    have hc0 : c ≠ 0 := norm_pos_iff.1 (lt_of_le_of_lt (le_max_right _ _) hc)
    have hV : balancedCore 𝕜 U ∈ 𝓝 (0 : Fₗ') := balancedCore_mem_nhds_zero hU
    have hb' : ∀ᶠ b in 𝓝 (0 : Fₗ'), c • b ∈ balancedCore 𝕜 U := by
      have ht := (continuous_const_smul c).tendsto (0 : Fₗ')
      rw [smul_zero] at ht
      exact ht hV
    filter_upwards [hb'] with b hb k hk
    have heq : k • b = (k * c⁻¹) • (c • b) := by
      rw [smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
    rw [heq]
    have hnorm : ‖k * c⁻¹‖ ≤ 1 := by
      rw [norm_mul, norm_inv, ← div_eq_mul_inv, div_le_one (norm_pos_iff.2 hc0)]
      exact (hr k hk).trans ((le_max_left _ _).trans hc.le)
    exact balancedCore_subset U
      ((balancedCore_balanced (𝕜 := 𝕜) U) (k * c⁻¹) hnorm
        (Set.smul_mem_smul_set (a := (k * c⁻¹ : 𝕜)) hb))
  have inner : ∀ a : StrongDual 𝕜 E', Continuous (smulRightLₗ 𝕜 E' Fₗ' a) := by
    intro a
    refine continuous_of_continuousAt_zero _ ?_
    unfold ContinuousAt
    rw [map_zero]
    refine (ContinuousLinearMap.hasBasis_nhds_zero).tendsto_right_iff.2 ?_
    rintro ⟨S, U⟩ ⟨hS, hU⟩
    have hK := hS.image a
    rw [NormedSpace.isVonNBounded_iff] at hK
    filter_upwards [key _ hK U hU] with b hb x hx
    exact hb _ ⟨x, hx, rfl⟩
  let L : StrongDual 𝕜 E' →ₗ[𝕜] Fₗ' →L[𝕜] E' →L[𝕜] Fₗ' :=
    { toFun := fun a => ⟨smulRightLₗ 𝕜 E' Fₗ' a, inner a⟩
      map_add' := fun a b => by
        ext x y
        first
          | simp
          | simp [smulRightLₗ, add_smul]
      map_smul' := fun c a => by
        ext x y
        first
          | simp
          | simp [smulRightLₗ, smul_smul, mul_comm] }
  refine ⟨⟨L, continuous_of_continuousAt_zero L ?_⟩, fun a b => rfl⟩
  unfold ContinuousAt
  rw [map_zero]
  refine (ContinuousLinearMap.hasBasis_nhds_zero).tendsto_right_iff.2 ?_
  rintro ⟨B, W⟩ ⟨hB, hW⟩
  obtain ⟨⟨S, U⟩, ⟨hS, hU⟩, hSU⟩ :=
    (ContinuousLinearMap.hasBasis_nhds_zero).mem_iff.1 hW
  have hVmem : balancedCore 𝕜 U ∈ 𝓝 (0 : Fₗ') := balancedCore_mem_nhds_zero hU
  obtain ⟨c, hc⟩ := (hB hVmem).exists
  have hε : (0 : ℝ) < 1 / (‖c‖ + 1) := by positivity
  have hN : {a : StrongDual 𝕜 E' | ∀ x ∈ S, a x ∈ Metric.ball (0 : 𝕜) (1 / (‖c‖ + 1))}
      ∈ 𝓝 (0 : StrongDual 𝕜 E') := by
    refine (ContinuousLinearMap.hasBasis_nhds_zero).mem_iff.2
      ⟨(S, Metric.ball (0 : 𝕜) (1 / (‖c‖ + 1))), ⟨hS, Metric.ball_mem_nhds 0 hε⟩, ?_⟩
    intro f hf
    exact hf
  filter_upwards [hN] with a ha
  intro b hb
  apply hSU
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Set.mem_smul_set.1 (hc hb)
  change a x • (c • v) ∈ U
  rw [smul_smul]
  have h1 := ha x hx
  rw [Metric.mem_ball, dist_zero_right] at h1
  have h2 : ‖a x‖ * (‖c‖ + 1) < 1 := by
    rw [← lt_div_iff₀ (by positivity : (0:ℝ) < ‖c‖ + 1)]
    exact h1
  have hnorm : ‖a x * c‖ ≤ 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg (a x), norm_nonneg c]
  exact balancedCore_subset U
    ((balancedCore_balanced (𝕜 := 𝕜) U) (a x * c) hnorm
      (Set.smul_mem_smul_set (a := (a x * c : 𝕜)) hv))
