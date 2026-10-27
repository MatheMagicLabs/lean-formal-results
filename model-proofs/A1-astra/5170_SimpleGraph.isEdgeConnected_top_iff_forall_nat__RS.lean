/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.isEdgeConnected_top_iff_forall_nat
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Connectivity/EdgeConnectivity.lean, line 187
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace SimpleGraph
variable {V : Type*} {G H : SimpleGraph V} {k l : ℕ∞} {u v w x y : V}
variable (G k u v) in
variable (G k) in

theorem isEdgeConnected_top_iff_forall_nat :
    G.IsEdgeConnected ⊤ ↔ ∀ n : ℕ, G.IsEdgeConnected n := by
  constructor
  · intro h n
    apply isEdgeConnected_iff.mpr
    intro s hs
    exact isEdgeConnected_iff.mp h (lt_of_lt_of_le hs le_top)
  · intro h
    apply isEdgeConnected_iff.mpr
    intro s hs
    have hex : ∃ n : ℕ, s.encard < n := by
      by_contra hn
      have ht : s.encard = ⊤ := ENat.eq_top_iff_forall_ge.mpr (by
        intro n
        exact le_of_not_gt (fun hlt => hn ⟨n, hlt⟩))
      exact (ne_of_lt hs) ht
    obtain ⟨n, hn⟩ := hex
    exact isEdgeConnected_iff.mp (h n) hn
