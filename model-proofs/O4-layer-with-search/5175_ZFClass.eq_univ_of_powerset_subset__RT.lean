/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFClass.eq_univ_of_powerset_subset
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 152
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

lemma eq_univ_of_powerset_subset (hA : powerset A ⊆ A) : A = .univ := by
  have h : ∀ x : ZFSet.{u}, x ∈ A := fun x =>
    ZFSet.inductionOn x fun x ih =>
      hA (ZFClass.mem_powerset.2 (by
        intro y hy
        exact ih y hy))
  first
    | exact Set.eq_univ_of_forall h
    | (ext y; exact ⟨fun _ => trivial, fun _ => h y⟩)
    | (ext y; simp [h])
    | (apply Set.ext; intro y; exact ⟨fun _ => trivial, fun _ => h y⟩)
