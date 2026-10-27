/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFClass.cmem_sInter
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 139
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  classical
  simp only [ZFClass.CMem]
  constructor
  · rintro ⟨b, hbEq, hb⟩ z ⟨c, hcEq, hc⟩
    refine ⟨b, hbEq, ?_⟩
    exact hb z ⟨c, hcEq, hc⟩
  · intro hB
    obtain ⟨a, ha⟩ := h
    obtain ⟨b, hb₁, hb₂⟩ :=
      hB (a : ZFClass) ⟨a, by simpa using ha⟩
    subst B
    have H : ∀ c : ZFSet, c ∈ A → b ∈ c := by
      intro c hc
      have hc' := hB (c : ZFClass) ⟨c, by simpa using hc⟩
      simpa using hc'
    refine ⟨b, rfl, ?_⟩
    intro t ht
    rcases ht with ⟨x, hxt, hx⟩
    rw [← hxt]
    exact H x hx
