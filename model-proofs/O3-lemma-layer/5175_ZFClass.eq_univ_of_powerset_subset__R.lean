/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFClass.eq_univ_of_powerset_subset
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 152
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  refine Set.eq_univ_of_forall (α := ZFSet.{u}) ?_
  intro x
  refine ZFSet.inductionOn x fun x ih => ?_
  refine hA ?_
  change (x : ZFClass.{u}) ⊆ A
  intro y hy
  first
    | exact ih y hy
    | exact ih y (coe_apply.1 hy)
    | exact ih y (by simpa using hy)
