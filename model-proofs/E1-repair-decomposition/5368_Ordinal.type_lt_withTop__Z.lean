/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ordinal.type_lt_withTop
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/Ordinal/Basic.lean, line 848
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm Z, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  let e : ((· < ·) : WithTop α → WithTop α → Prop) ≃r
      Sum.Lex ((· < ·) : α → α → Prop)
        (@emptyRelation PUnit.{u + 1}) :=
    { toEquiv :=
        { toFun := fun x =>
            match x with
            | none => Sum.inr PUnit.unit
            | some a => Sum.inl a
          invFun := fun x =>
            match x with
            | Sum.inl a => some a
            | Sum.inr _ => none
          left_inv := by
            intro x
            cases x <;> rfl
          right_inv := by
            intro x
            rcases x with a | ⟨⟩ <;> rfl }
      map_rel_iff' := by
        intro a b
        cases a <;> cases b <;> simp [emptyRelation] }
  exact Quot.sound ⟨e⟩
