/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFClass.eq_univ_of_powerset_subset
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 152
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 0 (round 0 = first attempt)
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

lemma eq_univ_of_powerset_subset (hA : powerset A ⊆ A) : A = .univ := by
  have h : ∀ x : ZFSet.{u}, x ∈ A := by
    intro x
    refine ZFSet.mem_wf.induction x ?_
    intro y ih
    apply hA
    apply mem_powerset.mpr
    intro z hz
    exact ih z hz
  ext x
  exact iff_of_true (h x) (by trivial)
