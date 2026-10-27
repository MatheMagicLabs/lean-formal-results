/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     mem_valueGroup_iff_exists_mk_of_comm
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Range.lean, line 306
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace MonoidWithZeroHom
open Set Subgroup Submonoid
section mrange
variable {G H : Type*} [MulZeroOneClass G] [MulZeroOneClass H] [Nontrivial H] (f : G →*₀ H)
end mrange
variable {A B : Type*}
section MonoidWithZeroHom
variable [MonoidWithZero A] [MonoidWithZero B] (f : A →*₀ B)
end MonoidWithZeroHom
noncomputable section Restrict
variable [MonoidWithZero A] [GroupWithZero B] {f : A →*₀ B}
variable (f) in
namespace ValueGroup₀
end ValueGroup₀
end Restrict
section GroupWithZero
variable [GroupWithZero A] [GroupWithZero B] {f : A →*₀ B}
variable (f)
set_option backward.isDefEq.respectTransparency false in
open Function
end GroupWithZero
section CommGroupWithZero
variable [MonoidWithZero A] [CommGroupWithZero B] (f : A →*₀ B)
namespace valueGroup
variable {r₁ s₁ r₂ s₂ : A}
end valueGroup

theorem mem_valueGroup_iff_exists_mk_of_comm (f : A →*₀ B) {y : Bˣ} :
    y ∈ f.valueGroup ↔ ∃ r s hr hs, y = valueGroup.mk f r s hr hs := by
  constructor
  · intro hy
    obtain ⟨r, s, hr, hs, h⟩ := valueGroup.exists_mk f ⟨y, hy⟩
    refine ⟨r, s, hr, hs, ?_⟩
    simpa using congrArg Subtype.val h
  · intro ⟨r, s, hr, hs, hy⟩
    rw [hy]
    exact (valueGroup.mk f r s hr hs).2
