/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFSet.choice_cmem
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 534
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
  first
    | letI : Definable₁ (fun y : ZFSet.{u} => Classical.epsilon fun z => z ∈ y) :=
        Classical.allZFSetDefinable _
      rw [map_fval yx]
    | letI : Definable 1 (fun s : Fin 1 → ZFSet.{u} =>
          (fun y : ZFSet.{u} => Classical.epsilon fun z => z ∈ y) (s 0)) :=
        Classical.allZFSetDefinable _
      rw [map_fval yx]
    | erw [map_fval yx]
  first
    | exact ⟨_, rfl, choice_mem_aux x h y yx⟩
    | exact ⟨_, rfl, Classical.epsilon_spec <| by_contradiction fun n => h <| by
         rwa [← (eq_empty y).2 fun z hz => n ⟨z, hz⟩]⟩
    | (refine ⟨_, rfl, ?_⟩
       show _ ∈ y
       exact choice_mem_aux x h y yx)
