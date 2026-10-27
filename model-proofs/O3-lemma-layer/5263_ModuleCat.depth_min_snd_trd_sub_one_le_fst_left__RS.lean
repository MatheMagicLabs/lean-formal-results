/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_min_snd_trd_sub_one_le_fst_left
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 230
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
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

lemma depth_min_snd_trd_sub_one_le_fst_left
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) (N : ModuleCat.{v} R) :
    S.X₂.depth N ⊓ (S.X₃.depth N - 1) ≤ S.X₁.depth N := by
  unfold ModuleCat.depth
  apply le_sSup
  intro i hi
  rcases lt_inf_iff.mp hi with ⟨h2, h3⟩
  obtain ⟨b, hb, hib⟩ := lt_sSup_iff.mp h2
  have s2 := hb i hib
  have h3' : (((i + 1 : ℕ)) : ℕ∞) <
      sSup {n : ℕ∞ | ∀ (i : ℕ), (i : ℕ∞) < n → Subsingleton (Ext S.X₃ N i)} := by
    generalize sSup {n : ℕ∞ | ∀ (i : ℕ), (i : ℕ∞) < n → Subsingleton (Ext S.X₃ N i)} = s
      at h3 ⊢
    induction s using ENat.recTopCoe with
    | top => exact ENat.coe_lt_top _
    | coe s =>
      have h : i < s - 1 := by exact_mod_cast h3
      exact_mod_cast (by omega : i + 1 < s)
  obtain ⟨c, hc, hic⟩ := lt_sSup_iff.mp h3'
  have s3 := hc (i + 1) hic
  refine subsingleton_of_forall_eq 0 (fun x => ?_)
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hS N x (add_comm 1 i)
    (Subsingleton.elim _ _)
  rw [← hy, Subsingleton.elim y 0]
  simp
