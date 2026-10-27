/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.map_bind
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/GiryMonad.lean, line 325
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  have hd (ν : Measure β) :
      ν.bind (fun b ↦ dirac (hg.mk g b)) = ν.map (hg.mk g) := by
    classical
    have hb : AEMeasurable (fun b ↦ dirac (hg.mk g b)) ν :=
      (measurable_dirac.comp hg.measurable_mk).aemeasurable
    ext s hs
    rw [bind_apply hs hb, map_apply hg.measurable_mk hs]
    have he : (fun b ↦ dirac (hg.mk g b) s) =
        (hg.mk g ⁻¹' s).indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
      funext b
      by_cases hb : hg.mk g b ∈ s <;>
        simp [dirac_apply', hs, hb]
    rw [he, lintegral_indicator (hs.preimage hg.measurable_mk)]
    simp
  have hgg : ∀ᵐ a ∂m, g =ᵐ[f a] hg.mk g :=
    ae_ae_of_ae_bind hf hg.ae_eq_mk
  calc
    map g (m.bind f) = map (hg.mk g) (m.bind f) :=
      map_congr hg.ae_eq_mk
    _ = (m.bind f).bind (fun b ↦ dirac (hg.mk g b)) :=
      (hd _).symm
    _ = m.bind (fun a ↦ (f a).bind (fun b ↦ dirac (hg.mk g b))) :=
      bind_bind hf (measurable_dirac.comp hg.measurable_mk).aemeasurable
    _ = m.bind (fun a ↦ map (hg.mk g) (f a)) := by
      simp only [hd]
    _ = m.bind (fun a ↦ map g (f a)) := by
      change join (map _ m) = join (map _ m)
      apply congrArg join
      apply map_congr
      filter_upwards [hgg] with a ha
      exact map_congr ha.symm
