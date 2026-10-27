/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFClass.cmem_sInter
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 139
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  by_cases hB : ∃ b : ZFSet.{u}, B = (b : ZFClass)
  · obtain ⟨b, rfl⟩ := hB
    simp [ZFClass.CMem]
    constructor
    · intro hb z x hx hxA
      subst z
      exact (mem_sInter.mp hb) x hxA
    · intro hb
      apply mem_sInter.mpr
      intro x hxA
      exact hb (x : ZFClass) x rfl hxA
  · have hn : ∀ D : ZFClass.{u}, ¬ B ᶜ∈ D := by
      intro D
      rintro ⟨b, hb₁, hb₂⟩
      apply hB
      refine ⟨b, ?_⟩
      first
      | exact hb₁
      | exact hb₂
      | exact hb₁.symm
      | exact hb₂.symm
    obtain ⟨a, ha⟩ := h
    have ha' : (a : ZFClass) ᶜ∈ A := by
      simpa [ZFClass.CMem] using ha
    constructor
    · intro hBA
      exact (hn _ hBA).elim
    · intro hBA
      exact (hn _ (hBA _ ha')).elim
