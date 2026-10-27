/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFSet.isOrdinal_notCMem_univ
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 559
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
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
  rw [ZFClass.cmem_univ]
  rintro ⟨x, h⟩
  have hm : ∀ y : ZFSet.{u}, y ∈ x ↔ IsOrdinal y := fun y => by
    show y ∈ x ↔ _
    exact Iff.of_eq (congrFun h y)
  have hxo : IsOrdinal x := by
    refine ⟨?_, ?_⟩
    · intro y hy z hz
      exact (hm z).2 (((hm y).1 hy).mem hz)
    · intro y z w hyz hzw hwx
      exact ((hm w).1 hwx).mem_trans hyz hzw
  exact mem_irrefl x ((hm x).2 hxo)
