/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFClass.eq_univ_of_powerset_subset
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 152
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
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

lemma eq_univ_of_powerset_subset (hA : powerset A ⊆ A) : A = .univ := by
  have h : ∀ x : ZFSet.{u}, x ∈ A := by
    intro x
    induction x using ZFSet.inductionOn with
    | _ x ih =>
      exact hA ih
  ext x
  constructor
  · intro _
    trivial
  · intro _
    exact h x
