/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.map_bind
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/GiryMonad.lean, line 325
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  let g' := hg.mk g
  have hg' : Measurable g' := hg.measurable_mk
  have hgg' : ∀ᵐ a ∂m, g =ᵐ[f a] g' :=
    ae_ae_of_ae_bind hf hg.ae_eq_mk
  have hmap : AEMeasurable (fun a ↦ map g' (f a)) m :=
    (measurable_map g' hg').comp_aemeasurable hf
  have heq : (fun a ↦ map g (f a)) =ᵐ[m] (fun a ↦ map g' (f a)) :=
    hgg'.mono fun a ha ↦ map_congr ha
  have hmapg : AEMeasurable (fun a ↦ map g (f a)) m :=
    hmap.congr heq.symm
  calc
    map g (bind m f) = map g' (bind m f) :=
      map_congr hg.ae_eq_mk
    _ = bind m (fun a ↦ map g' (f a)) := by
      ext s hs
      rw [map_apply hg' hs, bind_apply (hg' hs) hf, bind_apply hs hmap]
      apply lintegral_congr
      intro a
      exact (map_apply hg' hs).symm
    _ = bind m (fun a ↦ map g (f a)) := by
      ext s hs
      rw [bind_apply hs hmap, bind_apply hs hmapg]
      apply lintegral_congr_ae
      filter_upwards [heq] with a ha
      rw [ha]
