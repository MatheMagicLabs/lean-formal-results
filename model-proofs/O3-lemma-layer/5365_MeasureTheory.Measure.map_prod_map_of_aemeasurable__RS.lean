/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.map_prod_map_of_aemeasurable
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/Prod.lean, line 842
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

noncomputable section
open ENNReal MeasureTheory Set Function Real ENNReal MeasurableSpace MeasureTheory.Measure
open TopologicalSpace hiding generateFrom
open Filter hiding prod_eq map
variable {α β γ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable {μ μ' : Measure α} {ν ν' : Measure β} {τ : Measure γ}
namespace MeasureTheory
namespace Measure
variable [SFinite ν]
open IsUnifLocDoublingMeasure in
variable [SFinite μ]

theorem map_prod_map_of_aemeasurable {δ} [MeasurableSpace δ] {f : α → β} {g : γ → δ}
    (μa : Measure α) (μc : Measure γ) [SFinite μc] (hf : AEMeasurable f μa)
    (hg : AEMeasurable g μc) :
    (map f μa).prod (map g μc) = map (Prod.map f g) (μa.prod μc) := by
  have k1 : ∀ᵐ p ∂(μa.prod μc), f p.1 = hf.mk f p.1 := by
    have h := hf.ae_eq_mk
    rw [Filter.EventuallyEq, ae_iff] at h
    rw [ae_iff]
    apply measure_mono_null (t := Prod.fst ⁻¹' toMeasurable μa {a | ¬ f a = hf.mk f a})
    · intro p hp
      exact subset_toMeasurable μa _ hp
    · rw [prod_apply ((measurableSet_toMeasurable μa _).preimage measurable_fst)]
      refine le_antisymm ?_ (by simp)
      calc _ ≤ ∫⁻ x, (toMeasurable μa {a | ¬ f a = hf.mk f a}).indicator
              (fun _ => μc univ) x ∂μa := by
            refine lintegral_mono fun x => ?_
            by_cases hx : x ∈ toMeasurable μa {a | ¬ f a = hf.mk f a}
            · rw [indicator_of_mem hx]
              exact measure_mono (subset_univ _)
            · have : Prod.mk x ⁻¹' (Prod.fst ⁻¹'
                  toMeasurable μa {a | ¬ f a = hf.mk f a}) = (∅ : Set γ) := by
                ext y
                simp [hx]
              rw [this]
              simp
        _ = 0 := by
            rw [lintegral_indicator (measurableSet_toMeasurable _ _), setLIntegral_const,
              measure_toMeasurable, h, mul_zero]
  have k2 : ∀ᵐ p ∂(μa.prod μc), g p.2 = hg.mk g p.2 := by
    have h := hg.ae_eq_mk
    rw [Filter.EventuallyEq, ae_iff] at h
    rw [ae_iff]
    apply measure_mono_null (t := Prod.snd ⁻¹' toMeasurable μc {a | ¬ g a = hg.mk g a})
    · intro p hp
      exact subset_toMeasurable μc _ hp
    · rw [prod_apply ((measurableSet_toMeasurable μc _).preimage measurable_snd)]
      have : ∀ x : α, Prod.mk x ⁻¹' (Prod.snd ⁻¹'
          toMeasurable μc {a | ¬ g a = hg.mk g a}) = toMeasurable μc {a | ¬ g a = hg.mk g a} :=
        fun x => rfl
      simp only [this, measure_toMeasurable, h, lintegral_zero]
  have k : Prod.map f g =ᵐ[μa.prod μc] Prod.map (hf.mk f) (hg.mk g) := by
    filter_upwards [k1, k2] with p h1 h2
    exact Prod.ext h1 h2
  rw [map_congr hf.ae_eq_mk, map_congr hg.ae_eq_mk, map_congr k]
  ext s hs
  rw [map_apply (hf.measurable_mk.prodMap hg.measurable_mk) hs, prod_apply hs,
    prod_apply (hs.preimage (hf.measurable_mk.prodMap hg.measurable_mk)),
    lintegral_map (measurable_measure_prodMk_left hs) hf.measurable_mk]
  refine lintegral_congr fun x => ?_
  rw [map_apply hg.measurable_mk (measurable_prodMk_left hs)]
  rfl
