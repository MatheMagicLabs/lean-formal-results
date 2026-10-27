/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.map_bind
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Measure/GiryMonad.lean, line 325
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 2 (round 0 = first attempt)
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
  have hfg : AEMeasurable (fun a ↦ map g (f a)) m :=
    (aemeasurable_map (m := map f m) hg).comp_aemeasurable hf
  ext s hs
  have hpre : NullMeasurableSet (g ⁻¹' s) (m.bind f) := by
    apply (hs.preimage hg.measurable_mk).nullMeasurableSet.congr
    filter_upwards [hg.ae_eq_mk] with b hb
    simp only [mem_preimage, hb]
  rw [map_apply_of_aemeasurable hg hs, bind_apply₀ hpre hf,
    bind_apply₀ hs.nullMeasurableSet hfg]
  apply lintegral_congr_ae
  filter_upwards [AEMeasurable.ae_of_bind hf hg] with a ha
  exact (map_apply_of_aemeasurable ha hs).symm
