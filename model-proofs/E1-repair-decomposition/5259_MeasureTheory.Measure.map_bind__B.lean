/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.map_bind
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/GiryMonad.lean, line 325
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm B, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  have hgg' : g =ᵐ[m.bind f] g' := hg.ae_eq_mk
  have hgg'' : ∀ᵐ a ∂m, g =ᵐ[f a] g' := by
    first
    | exact ae_ae_of_ae_bind hf hgg'
    | exact ae_ae_of_ae_bind hgg' hf
    | exact ae_ae_of_ae_bind hgg'
  have hmap : Measurable (fun μ : Measure β ↦ map g' μ) := by
    first
    | exact measurable_map hg'
    | exact measurable_map
    | fun_prop
  calc
    map g (bind m f) = map g' (bind m f) := map_congr hgg'
    _ = bind m (fun a ↦ map g' (f a)) := by
      ext s hs
      have hleft :
          (bind m f) (g' ⁻¹' s) = ∫⁻ a, f a (g' ⁻¹' s) ∂m := by
        first
        | exact bind_apply (hg' hs) hf
        | exact bind_apply hf (hg' hs)
      have hright :
          (bind m (fun a ↦ map g' (f a))) s =
            ∫⁻ a, (map g' (f a)) s ∂m := by
        first
        | exact bind_apply hs (hmap.comp_aemeasurable hf)
        | exact bind_apply (hmap.comp_aemeasurable hf) hs
      rw [map_apply hg' hs, hleft, hright]
      simp only [map_apply hg' hs]
    _ = bind m (fun a ↦ map g (f a)) := by
      have h :
          (fun a ↦ map g' (f a)) =ᵐ[m] (fun a ↦ map g (f a)) := by
        filter_upwards [hgg''] with a ha
        exact (map_congr ha).symm
      first
      | exact bind_congr h
      | change (map (fun a ↦ map g' (f a)) m).join =
          (map (fun a ↦ map g (f a)) m).join
        exact congrArg Measure.join (map_congr h)
