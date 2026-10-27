/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFSet.choice_cmem
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 534
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
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
  have hmem : (Classical.epsilon fun z : ZFSet.{u} => z ∈ y) ∈ y :=
    choice_mem_aux x h y yx
  have hmap := @map_fval x y (fun (y : ZFSet.{u}) => Classical.epsilon fun z : ZFSet.{u} => z ∈ y)
    (Classical.allZFSetDefinable _) yx
  have heq : (choice x ′ y : ZFClass.{u}) = Classical.epsilon fun z : ZFSet.{u} => z ∈ y := by
    simpa [choice] using hmap
  refine ⟨Classical.epsilon fun z : ZFSet.{u} => z ∈ y, ?_, hmem⟩
  simpa using heq.symm
