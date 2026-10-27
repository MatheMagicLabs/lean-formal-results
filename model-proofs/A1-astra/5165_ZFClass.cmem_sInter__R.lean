/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFClass.cmem_sInter
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 139
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

universe u
namespace ZFClass
variable {A B C : ZFClass.{u}} {x y : ZFSet.{u}}
scoped notation:50 A:50 " ᶜ∈ " B:50 => ZFClass.CMem A B
scoped notation:50 A:50 " ᶜ∉ " B:50 => ¬ ZFClass.CMem A B
scoped under the `ZFClass` namespace. -/
scoped prefix:110 "⋃₀ " => ZFClass.sUnion
scoped prefix:110 "⋂₀ " => ZFClass.sInter
open scoped ZFSet in
open scoped ZFSet in

lemma cmem_sInter (h : A.Nonempty) : B ᶜ∈ ⋂₀ A ↔ ∀ z, z ᶜ∈ A → B ᶜ∈ z := by
  constructor
  · rintro ⟨b, rfl, hb⟩ z ⟨a, rfl, ha⟩
    refine ⟨b, rfl, ?_⟩
    rw [mem_sInter] at hb
    exact hb a ha
  · intro hB
    obtain ⟨a, ha⟩ := h
    obtain ⟨b, rfl, hb⟩ := hB _ ⟨a, rfl, ha⟩
    refine ⟨b, rfl, ?_⟩
    rw [mem_sInter]
    intro a ha
    obtain ⟨c, hc, hca⟩ := hB _ ⟨a, rfl, ha⟩
    have hcb : c = b := by
      apply ZFSet.ext
      intro t
      change t ∈ (c : ZFClass) ↔ t ∈ (b : ZFClass)
      rw [hc]
    simpa [hcb] using hca
