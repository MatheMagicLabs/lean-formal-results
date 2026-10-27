/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ordinal.type_lt_withBot
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/Ordinal/Basic.lean, line 854
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  let e : ((· < ·) : WithBot α → WithBot α → Prop) ≃r
      Sum.Lex ((· < ·) : PUnit.{u + 1} → PUnit.{u + 1} → Prop)
        ((· < ·) : α → α → Prop) :=
    { toEquiv :=
        { toFun := fun x => match x with
            | none => Sum.inl PUnit.unit
            | some a => Sum.inr a
          invFun := fun x => match x with
            | Sum.inl _ => none
            | Sum.inr a => some a
          left_inv := by
            intro x
            cases x <;> rfl
          right_inv := by
            intro x
            rcases x with x | x
            · cases x
              rfl
            · rfl }
      map_rel_iff' := by
        intro a b
        cases a <;> cases b <;> simp }
  exact Quotient.sound ⟨e⟩
