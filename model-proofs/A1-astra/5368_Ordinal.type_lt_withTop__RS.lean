/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ordinal.type_lt_withTop
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/Ordinal/Basic.lean, line 848
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
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
  let e : WithTop α ≃o (α ⊕ₗ PUnit.{u + 1}) :=
    { toFun := fun x =>
        match x with
        | none => toLex (Sum.inr PUnit.unit)
        | some a => toLex (Sum.inl a)
      invFun := fun x =>
        match ofLex x with
        | Sum.inl a => some a
        | Sum.inr _ => none
      left_inv := by
        intro x
        cases x <;> rfl
      right_inv := by
        intro x
        have hx : ∃ s : α ⊕ PUnit.{u + 1}, x = toLex s :=
          ⟨ofLex x, rfl⟩
        rcases hx with ⟨a | ⟨⟩, rfl⟩ <;> rfl
      map_rel_iff' := by
        intro x y
        cases x <;> cases y <;> simp }
  calc
    typeLT (WithTop α) = typeLT (α ⊕ₗ PUnit.{u + 1}) :=
      e.ordinalType_congr
    _ = typeLT α + 1 := by
      rw [type_lt_sum_lex]
      simp
      rfl
