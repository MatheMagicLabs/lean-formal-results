/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     mem_valueGroup_iff_exists_mk_of_comm
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Range.lean, line 306
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
      ((valueGroup.mk f r s hr hs : Bˣ) : B) = (f r)⁻¹ * f s := by
    simp [valueGroup.mk]
  constructor
  · intro hy
    induction hy using Subgroup.closure_induction with
    | mem u hu =>
        change ∃ r, f r = (u : B) at hu
        obtain ⟨r, hr⟩ := hu
        refine ⟨1, r, by simp, ?_, ?_⟩
        · rw [hr]
          exact Units.ne_zero u
        · apply Units.ext
          simp [mk_val, hr]
    | one =>
        refine ⟨1, 1, by simp, by simp, ?_⟩
        apply Units.ext
        simp [mk_val]
    | mul u v hu hv ihu ihv =>
        obtain ⟨r₁, s₁, hr₁, hs₁, rfl⟩ := ihu
        obtain ⟨r₂, s₂, hr₂, hs₂, rfl⟩ := ihv
        refine ⟨r₁ * r₂, s₁ * s₂, ?_, ?_, ?_⟩
        · simpa only [map_mul] using mul_ne_zero hr₁ hr₂
        · simpa only [map_mul] using mul_ne_zero hs₁ hs₂
        · apply Units.ext
          simp [mk_val, map_mul, div_eq_mul_inv, mul_comm,
            mul_left_comm, mul_assoc]
    | inv u hu ihu =>
        obtain ⟨r, s, hr, hs, rfl⟩ := ihu
        refine ⟨s, r, hs, hr, ?_⟩
        apply Units.ext
        simp [mk_val, div_eq_mul_inv, mul_comm]
  · rintro ⟨r, s, hr, hs, rfl⟩
    exact (valueGroup.mk f r s hr hs).property
