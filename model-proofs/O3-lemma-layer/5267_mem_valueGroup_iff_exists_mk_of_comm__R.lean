/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     mem_valueGroup_iff_exists_mk_of_comm
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Range.lean, line 306
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  · intro h
    first
      | unfold valueGroup at h
      | simp only [valueGroup] at h
      | skip
    induction h using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨1, a, by simp, by rw [ha]; exact x.ne_zero, ?_⟩
      ext
      simp [valueGroup.mk, ha]
    | one =>
      refine ⟨1, 1, by simp, by simp, ?_⟩
      ext
      simp [valueGroup.mk]
    | mul x y hx hy ihx ihy =>
      obtain ⟨r, s, hr, hs, rfl⟩ := ihx
      obtain ⟨r', s', hr', hs', rfl⟩ := ihy
      refine ⟨r * r', s * s', by simp [hr, hr'], by simp [hs, hs'], ?_⟩
      ext
      simp [valueGroup.mk, div_mul_div_comm]
      first
        | ac_rfl
        | simp only [mul_comm, mul_left_comm, mul_assoc]
        | (rw [mul_comm]; ac_rfl)
    | inv x hx ih =>
      obtain ⟨r, s, hr, hs, rfl⟩ := ih
      refine ⟨s, r, hs, hr, ?_⟩
      ext
      simp [valueGroup.mk]
      try first
        | ac_rfl
        | simp only [mul_inv, inv_inv, mul_comm]
  · rintro ⟨r, s, hr, hs, rfl⟩
    exact (valueGroup.mk f r s hr hs).2
