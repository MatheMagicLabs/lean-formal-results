/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ordinal.type_lt_withTop
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/Ordinal/Basic.lean, line 848
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  let e : WithTop α ≃ α ⊕ PUnit.{u + 1} :=
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
  have h :
      ((· < ·) : WithTop α → WithTop α → Prop) ≃r
        Sum.Lex ((· < ·) : α → α → Prop)
          ((· < ·) : PUnit.{u + 1} → PUnit.{u + 1} → Prop) :=
    { e with
      map_rel_iff' := by
        intro a b
        cases a <;> cases b <;> simp [e] }
  have ht :
      type ((· < ·) : WithTop α → WithTop α → Prop) =
        type (Sum.Lex ((· < ·) : α → α → Prop)
          ((· < ·) : PUnit.{u + 1} → PUnit.{u + 1} → Prop)) :=
    Quotient.sound ⟨h⟩
  have h1 :
      type ((· < ·) : PUnit.{u + 1} → PUnit.{u + 1} → Prop) =
        (1 : Ordinal.{u}) := by
    apply Quotient.sound
    refine ⟨{
      toFun := fun _ => default
      invFun := fun _ => PUnit.unit
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      map_rel_iff' := ?_ }⟩
    intro a b
    have hab : a = b := Subsingleton.elim _ _
    subst b
    simp
  have h1' :
      type (fun (_ _ : PUnit.{u + 1}) => False) = (1 : Ordinal.{u}) := by
    simpa using h1
  have ht' :
      typeLT (WithTop α) =
        typeLT α + type (fun (_ _ : PUnit.{u + 1}) => False) := by
    simpa using ht
  exact ht'.trans (congrArg (fun o => typeLT α + o) h1')
