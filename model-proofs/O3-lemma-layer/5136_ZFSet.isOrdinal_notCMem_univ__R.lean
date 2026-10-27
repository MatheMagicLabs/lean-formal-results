/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFSet.isOrdinal_notCMem_univ
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 559
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
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

theorem isOrdinal_notCMem_univ : {x | IsOrdinal x} ᶜ∉ (.univ : ZFClass.{u}) := by
  rintro ⟨x, hx, -⟩
  have key : ∀ y, y ∈ x ↔ IsOrdinal y := fun y => by
    have := congrArg (fun C : ZFClass.{u} => y ∈ C) hx
    first
      | exact Iff.of_eq this
      | simpa using this
  have hx' : IsOrdinal x :=
    ⟨fun y hy z hz => (key z).2 (((key y).1 hy).mem hz),
     fun hyz hzw hw => ((key _).1 hw).mem_trans hyz hzw⟩
  exact mem_irrefl x ((key x).2 hx')
