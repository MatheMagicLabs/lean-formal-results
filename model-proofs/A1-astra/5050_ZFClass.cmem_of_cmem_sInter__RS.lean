/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFClass.cmem_of_cmem_sInter
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 135
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

lemma cmem_of_cmem_sInter (hy : B ᶜ∈ ⋂₀ A) (hz : C ᶜ∈ A) : B ᶜ∈ C := by
  rcases hy with ⟨b, hb₁, hb₂⟩
  rcases hz with ⟨c, hc₁, hc₂⟩
  subst B
  subst C
  apply coe_cmem.mpr
  exact (mem_sInter.mp (by assumption)) c (by assumption)
