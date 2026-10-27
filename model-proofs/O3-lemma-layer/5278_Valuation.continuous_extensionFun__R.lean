/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.continuous_extensionFun
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 240
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Valuation ValuativeRel IsValuativeTopology UniformSpace MonoidWithZeroHom ValueGroup₀
open Set Filter Topology
variable {R K Γ₀ : Type*}
section Ring
namespace IsValuativeTopology
variable [Ring R] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)
open WithZeroTopology
end IsValuativeTopology
end Ring
section DivisionRing
variable [DivisionRing K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
section InversionEstimate
end InversionEstimate
namespace IsValuativeTopology
variable [ValuativeRel K] [TopologicalSpace K] [IsValuativeTopology K]
section WithZeroTopology
variable [v.Compatible]
open WithZeroTopology
end WithZeroTopology
end IsValuativeTopology
end DivisionRing
section Field
variable [Field K] [ValuativeRel K] [UniformSpace K] [IsValuativeTopology K]
namespace IsValuativeTopology
end IsValuativeTopology
namespace Valuation
variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) [v.Compatible]
open WithZeroTopology
variable [IsUniformAddGroup K]

private theorem continuous_extensionFun : Continuous v.extensionFun := by
  have hcont : Continuous v.restrict := by
    first
      | exact IsValuativeTopology.continuous_restrict v
      | exact v.continuous_restrict
      | exact continuous_restrict v
      | exact IsValuativeTopology.continuous_valuation v.restrict
      | exact IsValuativeTopology.continuous_valuation (v := v.restrict)
      | exact continuous_valuation v.restrict
      | exact continuous_valuation (v := v.restrict)
      | exact v.restrict.continuous_of_compatible
  refine Completion.isDenseInducing_coe.continuous_extend ?_
  intro x₀
  rcases eq_or_ne x₀ 0 with (rfl | h)
  · refine ⟨0, ?_⟩
    have := Completion.isDenseInducing_coe.isInducing.nhds_eq_comap (0 : K)
    rw [Completion.coe_zero] at this
    rw [← this]
    exact hcont.tendsto' 0 0 (map_zero v.restrict)
  · have preimage_one : v.restrict ⁻¹' {1} ∈ 𝓝 (1 : K) := by
      apply hcont.continuousAt.preimage_mem_nhds
      rw [map_one]
      exact WithZeroTopology.singleton_mem_nhds_of_ne_zero one_ne_zero
    obtain ⟨V, V_in, hV⟩ : ∃ V ∈ 𝓝 (1 : Completion K),
        ∀ x : K, (x : Completion K) ∈ V → v.restrict x = 1 := by
      rwa [Completion.isDenseInducing_coe.nhds_eq_comap, mem_comap] at preimage_one
    have : ∃ V' ∈ 𝓝 (1 : Completion K), (0 : Completion K) ∉ V' ∧
        ∀ (x) (_ : x ∈ V') (y) (_ : y ∈ V'), x * y⁻¹ ∈ V := by
      have : Tendsto (fun p : Completion K × Completion K => p.1 * p.2⁻¹)
          ((𝓝 1) ×ˢ (𝓝 1)) (𝓝 1) := by
        rw [← nhds_prod_eq]
        conv =>
          congr
          rfl
          rfl
          rw [← one_mul (1 : Completion K)]
        refine
          Tendsto.mul continuous_fst.continuousAt (Tendsto.comp ?_ continuous_snd.continuousAt)
        convert (continuousAt_inv₀ (zero_ne_one.symm : 1 ≠ (0 : Completion K))).tendsto
        exact inv_one.symm
      rcases tendsto_prod_self_iff.mp this V V_in with ⟨U, U_in, hU⟩
      let hatKstar := ({0}ᶜ : Set <| Completion K)
      have : hatKstar ∈ 𝓝 (1 : Completion K) := compl_singleton_mem_nhds zero_ne_one.symm
      use U ∩ hatKstar, Filter.inter_mem U_in this
      constructor
      · rintro ⟨_, h'⟩
        rw [mem_compl_singleton_iff] at h'
        exact h' rfl
      · rintro x ⟨hx, _⟩ y ⟨hy, _⟩
        apply hU <;> assumption
    rcases this with ⟨V', V'_in, zeroV', hV'⟩
    have nhds_right : (fun x => x * x₀) '' V' ∈ 𝓝 x₀ := by
      have l : Function.LeftInverse (fun x : Completion K => x * x₀⁻¹)
          fun x : Completion K => x * x₀ := by
        intro x
        simp only [mul_assoc, mul_inv_cancel₀ h, mul_one]
      have r : Function.RightInverse (fun x : Completion K => x * x₀⁻¹)
          fun x : Completion K => x * x₀ := by
        intro x
        simp only [mul_assoc, inv_mul_cancel₀ h, mul_one]
      have c : Continuous fun x : Completion K => x * x₀⁻¹ :=
        continuous_id.mul continuous_const
      rw [image_eq_preimage_of_inverse l r]
      rw [← mul_inv_cancel₀ h] at V'_in
      exact c.continuousAt V'_in
    have : ∃ z₀ : K, ∃ y₀ ∈ V', (z₀ : Completion K) = y₀ * x₀ ∧ z₀ ≠ 0 := by
      rcases Completion.denseRange_coe.mem_nhds nhds_right with
        ⟨z₀, y₀, y₀_in, H : y₀ * x₀ = z₀⟩
      refine ⟨z₀, y₀, y₀_in, ⟨H.symm, ?_⟩⟩
      rintro rfl
      exact mul_ne_zero (ne_of_mem_of_not_mem y₀_in zeroV') h (by rw [H]; simp)
    rcases this with ⟨z₀, y₀, y₀_in, hz₀, z₀_ne⟩
    have vz₀_ne : v.restrict z₀ ≠ 0 := by rwa [Valuation.ne_zero_iff]
    refine ⟨v.restrict z₀, ?_⟩
    rw [WithZeroTopology.tendsto_of_ne_zero vz₀_ne, eventually_comap]
    filter_upwards [nhds_right] with x x_in a ha
    rcases x_in with ⟨y, y_in, rfl⟩
    have : v.restrict (a * z₀⁻¹) = 1 := by
      apply hV
      have : ((z₀⁻¹ : K) : Completion K) = (z₀ : Completion K)⁻¹ :=
        map_inv₀ (Completion.coeRingHom : K →+* Completion K) z₀
      rw [Completion.coe_mul, this, ha, hz₀, mul_inv, mul_comm y₀⁻¹, ← mul_assoc, mul_assoc y,
        mul_inv_cancel₀ h, mul_one]
      solve_by_elim
    calc
      v.restrict a = v.restrict (a * z₀⁻¹ * z₀) := by
        rw [mul_assoc, inv_mul_cancel₀ z₀_ne, mul_one]
      _ = v.restrict (a * z₀⁻¹) * v.restrict z₀ := Valuation.map_mul _ _ _
      _ = v.restrict z₀ := by rw [this, one_mul]
