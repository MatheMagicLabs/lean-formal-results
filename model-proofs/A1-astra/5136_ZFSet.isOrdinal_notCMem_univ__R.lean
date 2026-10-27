/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFSet.isOrdinal_notCMem_univ
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 559
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
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
  intro h
  rcases h with ⟨s, hs, ht⟩
  have hm (z : ZFSet.{u}) : z ∈ s ↔ IsOrdinal z := by
    first
    | exact (congrArg (fun C : ZFClass.{u} => z ∈ C) hs).to_iff
    | exact (congrArg (fun C : ZFClass.{u} => z ∈ C) hs).to_iff.symm
    | exact (congrArg (fun C : ZFClass.{u} => z ∈ C) ht).to_iff
    | exact (congrArg (fun C : ZFClass.{u} => z ∈ C) ht).to_iff.symm
  have ho : IsOrdinal s := by
    constructor
    · intro y hy z hz
      apply (hm z).2
      have hy' := (hm y).1 hy
      constructor
      · intro w hw v hv
        exact hy'.2 hv hw hz
      · intro a b c hab hbc hcz
        exact hy'.2 hab hbc (hy'.1 z hz hcz)
    · intro a b c hab hbc hcs
      exact ((hm c).1 hcs).1 b hbc hab
  have hss : s ∈ s := (hm s).2 ho
  first
  | exact (mem_irrefl s) hss
  | exact (mem_wf.irrefl s) hss
  | exact (irrefl s) hss
