/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_iff
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 124
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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

lemma depth_eq_iff (N M : ModuleCat.{v} R) (n : ℕ) : N.depth M = n ↔
    Nontrivial (Ext N M n) ∧ ∀ i < n, Subsingleton (Ext N M i) := by
  classical
  let d : ℕ∞ := ⨅ i : ℕ, ⨅ (_ : Nontrivial (Ext N M i)), (i : ℕ∞)
  have upper (i : ℕ) (hi : Nontrivial (Ext N M i)) :
      d ≤ (i : ℕ∞) :=
    iInf_le_of_le i (iInf_le_of_le hi le_rfl)
  have lower (k : ℕ)
      (hk : ∀ i, Nontrivial (Ext N M i) → k ≤ i) :
      (k : ℕ∞) ≤ d := by
    refine le_iInf fun i => le_iInf fun hi => ?_
    exact_mod_cast hk i hi
  have hdepth : N.depth M = d := by
    change sSup {a : ℕ∞ |
      ∀ i : ℕ, (i : ℕ∞) < a → Subsingleton (Ext N M i)} = d
    apply le_antisymm
    · refine sSup_le fun a ha => ?_
      refine le_iInf fun i => le_iInf fun hi => ?_
      by_contra h
      haveI := ha i (lt_of_not_ge h)
      rcases hi with ⟨⟨x, y, hxy⟩⟩
      exact hxy (Subsingleton.elim x y)
    · apply le_sSup
      intro i hid
      rcases subsingleton_or_nontrivial (Ext N M i) with hi | hi
      · exact hi
      · exact False.elim ((not_le_of_gt hid) (upper i hi))
  rw [hdepth]
  constructor
  · intro hd
    have hv : ∀ i < n, Subsingleton (Ext N M i) := by
      intro i hin
      rcases subsingleton_or_nontrivial (Ext N M i) with hi | hi
      · exact hi
      · have h := upper i hi
        rw [hd] at h
        have hni : n ≤ i := by exact_mod_cast h
        omega
    refine ⟨?_, hv⟩
    by_contra hn
    have hnext : ((n + 1 : ℕ) : ℕ∞) ≤ d := by
      apply lower
      intro i hi
      have h := upper i hi
      rw [hd] at h
      have hni : n ≤ i := by exact_mod_cast h
      have hne : i ≠ n := by
        intro he
        subst i
        exact hn hi
      omega
    rw [hd] at hnext
    have hbad : n + 1 ≤ n := by exact_mod_cast hnext
    omega
  · rintro ⟨hn, hv⟩
    refine le_antisymm (upper n hn) (lower n ?_)
    intro i hi
    by_contra hni
    have hin : i < n := by omega
    haveI := hv i hin
    rcases hi with ⟨⟨x, y, hxy⟩⟩
    exact hxy (Subsingleton.elim x y)
