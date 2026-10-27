/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ordinal.type_lt_withTop
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/Ordinal/Basic.lean, line 848
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
theorem type_lt_withTop {α : Type u} [LinearOrder α] [WellFoundedLT α] :
    typeLT (WithTop α) = typeLT α + 1 := by
  change type ((· < ·) : WithTop α → WithTop α → Prop) =
    type (Sum.Lex ((· < ·) : α → α → Prop)
      (fun (_ _ : PUnit.{u + 1}) => False))
  apply Quotient.sound
  refine ⟨?_⟩
  refine
    { toEquiv :=
        { toFun := fun x =>
            match x with
            | none => Sum.inr PUnit.unit
            | some a => Sum.inl a
          invFun := fun x =>
            match x with
            | Sum.inl a => some a
            | Sum.inr _ => none
          left_inv := ?_
          right_inv := ?_ }
      map_rel_iff' := ?_ }
  · intro x
    cases x <;> rfl
  · intro x
    rcases x with a | ⟨⟩ <;> rfl
  · intro a b
    cases a <;> cases b <;> simp
