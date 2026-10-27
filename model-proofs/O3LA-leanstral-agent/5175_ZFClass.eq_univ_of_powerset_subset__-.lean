/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFClass.eq_univ_of_powerset_subset
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 152
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

lemma eq_univ_of_powerset_subset (hA : powerset A ⊆ A) : A = .univ := by
  ext x
  refine ⟨fun _ => by simp, fun _ => ?_⟩
  refine x.inductionOn fun x IH => ?_
  have hx_sub : (x : ZFClass) ⊆ A := by
    intro y hy
    simpa using IH y hy
  exact hA hx_sub
