/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.map_bind
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/GiryMonad.lean, line 325
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

noncomputable section
open ENNReal Set Filter
variable {α β : Type*}
namespace MeasureTheory
namespace Measure
variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

theorem map_bind {γ} [MeasurableSpace γ] {m : Measure α} {f : α → Measure β} {g : β → γ}
    (hf : AEMeasurable f m) (hg : AEMeasurable g (m.bind f)) :
    map g (bind m f) = bind m fun a ↦ map g (f a) := by
  obtain ⟨g', hg'meas, hgg'⟩ := hg
  have key : ∀ᵐ a ∂m, g =ᵐ[f a] g' := by
    obtain ⟨t, hst, ht, ht0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgg')
    rw [bind_apply ht hf] at ht0
    have hmeas : AEMeasurable (fun a => f a t) m :=
      (measurable_coe ht).comp_aemeasurable hf
    have h2 := (lintegral_eq_zero_iff' hmeas).1 ht0
    filter_upwards [h2] with a ha
    exact ae_iff.2 (measure_mono_null hst (by simpa using ha))
  rw [map_congr hgg']
  have : bind m (fun a => map g (f a)) = bind m (fun a => map g' (f a)) := by
    unfold Measure.bind
    rw [map_congr (key.mono fun a ha => map_congr ha)]
  rw [this]
  have hk : AEMeasurable (fun a => map g' (f a)) m :=
    (measurable_map g' hg'meas).comp_aemeasurable hf
  ext s hs
  rw [map_apply hg'meas hs, bind_apply (hg'meas hs) hf, bind_apply hs hk]
  exact lintegral_congr fun a => (map_apply hg'meas hs).symm
