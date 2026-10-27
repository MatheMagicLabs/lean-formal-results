/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ordinal.type_lt_withBot
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/Ordinal/Basic.lean, line 854
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

noncomputable section
open Function Cardinal Set Equiv Order
open scoped Cardinal InitialSeg
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
attribute [instance] WellOrder.wo
namespace WellOrder
end WellOrder
namespace Ordinal
scoped notation3 "typeLT " α:70 => @Ordinal.type α (· < ·) inferInstance
open scoped Classical in
open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
variable (r) in

@[simp]
theorem type_lt_withBot {α : Type u} [LinearOrder α] [WellFoundedLT α] :
    typeLT (WithBot α) = 1 + typeLT α := by
  rw [WithBot.orderIsoPUnitSumLex.ordinalType_congr]
  change type (Sum.Lex (α := PUnit.{u+1}) (β := α) (· < ·) (· < ·)) = _
  rw [type_sum_lex, type_eq_one_of_unique]
