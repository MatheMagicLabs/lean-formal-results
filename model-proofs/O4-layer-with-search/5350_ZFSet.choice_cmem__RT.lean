/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFSet.choice_cmem
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 534
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
end ZFClass
namespace Class
set_option linter.deprecatedCoercions false
scoped under the `Class` namespace. -/
scoped prefix:110 "⋃₀ " => Class.sUnion
scoped prefix:110 "⋂₀ " => Class.sInter
set_option linter.deprecated.deprecatedTarget false in
open scoped ZFSet in
open scoped ZFSet in
end Class
open scoped ZFClass
namespace ZFSet
variable {x y : ZFSet.{u}}
variable (x : ZFSet.{u})

theorem choice_cmem (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y ∈ x) : choice x ′ y ᶜ∈ y := by
  delta choice
  rw [@map_fval _ _ _ (Classical.allZFSetDefinable _) yx, ZFClass.coe_cmem]
  exact choice_mem_aux x h y yx
