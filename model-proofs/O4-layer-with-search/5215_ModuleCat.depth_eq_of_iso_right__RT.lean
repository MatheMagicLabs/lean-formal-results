/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_of_iso_right
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 184
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
  have key : ∀ i : ℕ, Nonempty (Ext N M i ≃ Ext N M' i) := fun i => ⟨{
    toFun := fun α => α.comp (Ext.mk₀ e.hom) (add_zero i)
    invFun := fun α => α.comp (Ext.mk₀ e.inv) (add_zero i)
    left_inv := fun α => by
      simp only
      rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e.hom_inv_id,
        Ext.comp_mk₀_id]
    right_inv := fun α => by
      simp only
      rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e.inv_hom_id,
        Ext.comp_mk₀_id] }⟩
  rw [depth_eq_sSup_lt_top, depth_eq_sSup_lt_top]
  congr 1
  ext n
  simp only [Set.mem_setOf_eq]
  refine and_congr Iff.rfl (forall_congr' fun i => imp_congr_right fun _ => ?_)
  obtain ⟨f⟩ := key i
  exact ⟨fun h => @Equiv.subsingleton _ _ f.symm h,
    fun h => @Equiv.subsingleton _ _ f h⟩
