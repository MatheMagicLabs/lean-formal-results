/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_top_iff
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 96
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
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

lemma depth_eq_top_iff (N M : ModuleCat.{v} R) :
    N.depth M = ⊤ ↔ ∀ i, Subsingleton (Ext N M i) := by
  dsimp [ModuleCat.depth]
  rw [sSup_eq_top]
  constructor
  · intro h i
    by_contra hns
    have hnontriv : Nontrivial (Ext N M i) := by
      by_contra hnot
      apply hns
      exact (not_nontrivial_iff_subsingleton.mp hnot)
    have hb_lt_top : (i + 1 : ℕ∞) < ⊤ := by
      exact ENat.coe_lt_top (i + 1)
    rcases h (i + 1 : ℕ∞) hb_lt_top with ⟨a, ha, hba⟩
    have hi_lt_a : (i : ℕ∞) < a := by
      calc
        (i : ℕ∞) < (i + 1 : ℕ∞) := by
          norm_cast
          omega
        _ < a := hba
    have hsubsingleton : Subsingleton (Ext N M i) := ha i hi_lt_a
    have : ¬ Nontrivial (Ext N M i) := not_nontrivial_iff_subsingleton.mpr hsubsingleton
    exact this hnontriv
  · intro h b hb
    refine ⟨⊤, ?_, hb⟩
    intro i hi
    exact h i
