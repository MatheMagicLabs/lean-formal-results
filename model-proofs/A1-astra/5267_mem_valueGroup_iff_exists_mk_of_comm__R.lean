/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     mem_valueGroup_iff_exists_mk_of_comm
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Range.lean, line 306
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  classical
  have mk_val (r s : A) (hr : f r ≠ 0) (hs : f s ≠ 0) :
      ((valueGroup.mk f r s hr hs : Bˣ) : B) = f s / f r := by
    simp [valueGroup.mk, div_eq_mul_inv, mul_comm]
  let S : Subgroup Bˣ :=
    { carrier := {u | ∃ r s hr hs, u = valueGroup.mk f r s hr hs}
      one_mem' := by
        refine ⟨1, 1, by simp, by simp, ?_⟩
        apply Units.ext
        simp [mk_val]
      mul_mem' := by
        rintro u v ⟨r₁, s₁, hr₁, hs₁, rfl⟩
          ⟨r₂, s₂, hr₂, hs₂, rfl⟩
        refine ⟨r₁ * r₂, s₁ * s₂,
          by simpa using mul_ne_zero hr₁ hr₂,
          by simpa using mul_ne_zero hs₁ hs₂, ?_⟩
        apply Units.ext
        simp [mk_val, map_mul, div_mul_div_comm]
      inv_mem' := by
        rintro u ⟨r, s, hr, hs, rfl⟩
        refine ⟨s, r, hs, hr, ?_⟩
        apply Units.ext
        simp [mk_val] }
  have hS : f.valueGroup ≤ S := by
    change Subgroup.closure _ ≤ S
    apply (Subgroup.closure_le S).mpr
    intro u hu
    change ∃ r, f r = (u : B) at hu
    obtain ⟨r, hr⟩ := hu
    have hr₀ : f r ≠ 0 := by
      rw [hr]
      exact Units.ne_zero u
    change ∃ r s hr hs, u = valueGroup.mk f r s hr hs
    refine ⟨1, r, by simp, hr₀, ?_⟩
    apply Units.ext
    simp [mk_val, hr]
  constructor
  · exact fun hy => hS hy
  · rintro ⟨r, s, hr, hs, rfl⟩
    exact (valueGroup.mk f r s hr hs).property
