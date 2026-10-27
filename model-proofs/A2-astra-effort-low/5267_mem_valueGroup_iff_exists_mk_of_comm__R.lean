/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     mem_valueGroup_iff_exists_mk_of_comm
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Range.lean, line 306
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
        change ∃ r, f r = (y : B) at hy
        obtain ⟨r, hr⟩ := hy
        refine ⟨1, r, ?_, ?_, ?_⟩
        · simp
        · rw [hr]
          exact y.ne_zero
        · apply Units.ext
          simp [valueGroup.mk, hr]
    | one =>
        refine ⟨1, 1, by simp, by simp, ?_⟩
        apply Units.ext
        simp [valueGroup.mk]
    | mul y z hy hz ihy ihz =>
        obtain ⟨r₁, s₁, hr₁, hs₁, rfl⟩ := ihy
        obtain ⟨r₂, s₂, hr₂, hs₂, rfl⟩ := ihz
        refine ⟨r₁ * r₂, s₁ * s₂, ?_, ?_, ?_⟩
        · simpa only [map_mul] using mul_ne_zero hr₁ hr₂
        · simpa only [map_mul] using mul_ne_zero hs₁ hs₂
        · apply Units.ext
          simp [valueGroup.mk, map_mul, mul_div_mul_comm]
          ac_rfl
    | inv y hy ih =>
        obtain ⟨r, s, hr, hs, rfl⟩ := ih
        refine ⟨s, r, hs, hr, ?_⟩
        apply Units.ext
        simp [valueGroup.mk]
  · rintro ⟨r, s, hr, hs, rfl⟩
    exact (valueGroup.mk f r s hr hs).property
