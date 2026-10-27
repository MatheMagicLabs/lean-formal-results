/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_of_iso_right
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 184
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open IsLocalRing LinearMap Module
universe v u
open RingTheory.Sequence Ideal CategoryTheory Abelian Limits Pointwise ModuleCat IsSMulRegular
variable {R : Type u} [CommRing R] [Small.{v} R]
section depth
namespace ModuleCat
open Classical in

lemma depth_eq_of_iso_right (N : ModuleCat.{v} R) {M M' : ModuleCat.{v} R} (e : M ≅ M') :
    N.depth M = N.depth M' := by
  have key : ∀ {A B : ModuleCat.{v} R} (f : A ≅ B) (i : ℕ),
      Subsingleton (Ext N B i) → Subsingleton (Ext N A i) := by
    intro A B f i h
    have hx : ∀ x : Ext N A i,
        x = (x.comp (Ext.mk₀ f.hom) (add_zero i)).comp (Ext.mk₀ f.inv) (add_zero i) := by
      intro x
      rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id,
        Ext.comp_mk₀_id]
    constructor
    intro x y
    rw [hx x, hx y, Subsingleton.elim (x.comp (Ext.mk₀ f.hom) (add_zero i))
      (y.comp (Ext.mk₀ f.hom) (add_zero i))]
  rw [depth_eq_sSup_lt_top, depth_eq_sSup_lt_top]
  congr 1
  ext n
  simp only [Set.mem_setOf_eq]
  exact and_congr_right fun _ => forall_congr' fun i =>
    imp_congr_right fun _ => ⟨key e.symm i, key e i⟩
