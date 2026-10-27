/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_sSup_lt_top
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 144
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

lemma depth_eq_sSup_lt_top (N M : ModuleCat.{v} R) : N.depth M =
    sSup {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} := by
  dsimp [ModuleCat.depth]
  set S := {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (Ext N M i)}
  set T := {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)}
  have hST : T ⊆ S := fun n hn => hn.2
  have hBddT : BddAbove T := OrderTop.bddAbove _
  have hBddS : BddAbove S := OrderTop.bddAbove _
  apply le_antisymm
  · by_cases htop : ⊤ ∈ S
    · have hall : ∀ i : ℕ, Subsingleton (Ext N M i) := by
        intro i
        exact htop i (ENat.natCast_lt_top i)
      have hNatSubsetT : ∀ n : ℕ, (n : ℕ∞) ∈ T := by
        intro n
        refine ⟨ENat.natCast_lt_top n, fun i _ => hall i⟩
      have hSupT : sSup T = ⊤ := by
        have hrange : Set.range (fun n : ℕ => (n : ℕ∞)) ⊆ T := by
          rintro x ⟨n, rfl⟩; exact hNatSubsetT n
        have hSupNat : sSup (Set.range (fun n : ℕ => (n : ℕ∞))) = ⊤ := by
          rw [sSup_range, ENat.iSup_natCast]
        apply le_antisymm le_top
        calc
          ⊤ = sSup (Set.range (fun n : ℕ => (n : ℕ∞))) := by rw [hSupNat]
          _ ≤ sSup T := csSup_le_csSup' (OrderTop.bddAbove _) hrange
      rw [csSup_eq_top_of_top_mem htop, hSupT]
    · have hST' : S ⊆ T := by
        intro n hn
        refine ⟨?_, hn⟩
        by_contra! hge
        have hn_top : n = ⊤ := le_antisymm le_top hge
        rw [hn_top] at hn
        exact htop hn
      exact csSup_le_csSup' hBddT hST'
  · exact csSup_le_csSup' hBddS hST
