/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.hasBasis_nhds_coe_zero
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 430
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 3 (round 0 = first attempt)
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

theorem hasBasis_nhds_coe_zero :
    (𝓝 (0 : Completion K)).HasBasis (fun _ ↦ True)
      fun γ : v.extension.ValueGroup₀ˣ ↦ {x | v.extension.restrict x < γ.1} := by
  have hB := (v.hasBasis_nhds_zero).hasBasis_of_isDenseInducing
    Completion.isDenseInducing_coe
  simp only [closure_image_coe_ofPred_restrict_lt, Completion.coe_zero] at hB
  have hc : ∀ y : K, v.extension (y : Completion K) = v y := by
    intro y
    first
    | exact v.extension_coe y
    | exact Valuation.extension_coe v y
    | exact v.extension_extends y
    | simp [Valuation.extension_coe]
    | simp [Valuation.extension_extends]
    | simp [Valuation.extension]
  have key : ∀ (x : Completion K) (γ' : v.extension.ValueGroup₀ˣ),
      v.extension.restrict x < γ'.1 ↔ v.extension x < embedding γ'.1 := by
    intro x γ'
    first
    | exact Iff.rfl
    | (rw [← (ValueGroup₀.embedding_strictMono).lt_iff_lt]; simp)
    | (rw [← (ValueGroup₀.embedding_strictMono).lt_iff_lt]; rfl)
  have key2 : ∀ (x y : Completion K),
      v.extension.restrict x < v.extension.restrict y ↔ v.extension x < v.extension y := by
    intro x y
    first
    | exact Iff.rfl
    | (rw [← (ValueGroup₀.embedding_strictMono).lt_iff_lt]; simp)
    | (rw [← (ValueGroup₀.embedding_strictMono).lt_iff_lt]; rfl)
  have happrox : ∀ z : Completion K, z ≠ 0 → ∃ y : K, v y = v.extension z := by
    intro z hz
    have hcompl : ({z}ᶜ : Set (Completion K)) ∈ 𝓝 (0 : Completion K) := by
      first
      | exact compl_singleton_mem_nhds hz.symm
      | exact isOpen_compl_singleton.mem_nhds hz.symm
    obtain ⟨γ, -, hγ⟩ := hB.mem_iff.1 hcompl
    have hle : embedding γ.1 ≤ v.extension z := not_lt.1 fun h => hγ h rfl
    have hS : {x : Completion K | v.extension x < embedding γ.1} ∈ 𝓝 (0 : Completion K) :=
      hB.mem_of_mem trivial
    have hT : (fun x => x - z) ⁻¹' {x : Completion K | v.extension x < embedding γ.1}
        ∈ 𝓝 z := by
      apply (continuous_sub_right z).continuousAt.preimage_mem_nhds
      show _ ∈ 𝓝 (z - z)
      rw [sub_self]
      exact hS
    obtain ⟨w, hw, y, rfl⟩ := mem_closure_iff_nhds.1 (Completion.denseRange_coe z) _ hT
    refine ⟨y, ?_⟩
    rw [← hc]
    have hw' : v.extension ((y : Completion K) - z) < embedding γ.1 := hw
    exact v.extension.map_eq_of_sub_lt (lt_of_lt_of_le hw' hle)
  refine ⟨fun t => ?_⟩
  constructor
  · intro ht
    obtain ⟨γ, -, hγ⟩ := hB.mem_iff.1 ht
    obtain ⟨r, s, hr, hs, h⟩ := Valuation.exists_div_eq_of_unit (v := v) γ
    have he : embedding γ.1 = v r / v s := by
      first
      | (rw [← h, map_div₀]; rfl)
      | (rw [← h]; simp)
    have hr' : 0 < v.extension.restrict (r : Completion K) := by
      have := (key2 0 (r : Completion K)).2 (by rw [map_zero, hc]; exact hr)
      rwa [map_zero] at this
    have hs' : 0 < v.extension.restrict (s : Completion K) := by
      have := (key2 0 (s : Completion K)).2 (by rw [map_zero, hc]; exact hs)
      rwa [map_zero] at this
    have ha : v.extension.restrict (r : Completion K) / v.extension.restrict (s : Completion K) ≠ 0 :=
      div_ne_zero hr'.ne' hs'.ne'
    refine ⟨Units.mk0 _ ha, trivial, ?_⟩
    intro x hx
    apply hγ
    show v.extension x < embedding γ.1
    rw [he]
    have hx' : v.extension.restrict x < v.extension.restrict (r : Completion K) /
        v.extension.restrict (s : Completion K) := hx
    rw [← map_div₀] at hx'
    have := (key2 _ _).1 hx'
    rwa [map_div₀, hc, hc] at this
  · rintro ⟨γ', -, hγ'⟩
    obtain ⟨a, b, ha, hb, hab⟩ := Valuation.exists_div_eq_of_unit (v := v.extension) γ'
    obtain ⟨ya, hya⟩ := happrox a (fun h0 => by simp [h0] at ha)
    obtain ⟨yb, hyb⟩ := happrox b (fun h0 => by simp [h0] at hb)
    have h1 : (embedding (v.restrict (ya / yb)) : Γ₀) = v (ya / yb) := by
      first
      | rfl
      | simp
    have hne : v.restrict (ya / yb) ≠ 0 := by
      intro h0
      rw [h0, map_zero, map_div₀, hya, hyb] at h1
      exact div_ne_zero ha.ne' hb.ne' h1.symm
    refine hB.mem_iff.2 ⟨Units.mk0 _ hne, trivial, fun x hx => hγ' ?_⟩
    show v.extension.restrict x < γ'.1
    rw [key]
    have he' : embedding γ'.1 = v.extension a / v.extension b := by
      first
      | (rw [← hab, map_div₀]; rfl)
      | (rw [← hab]; simp)
    rw [he', ← hya, ← hyb, ← map_div₀, ← h1]
    exact hx
