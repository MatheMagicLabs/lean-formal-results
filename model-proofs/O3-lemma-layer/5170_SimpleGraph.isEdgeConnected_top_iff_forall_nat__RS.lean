/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.isEdgeConnected_top_iff_forall_nat
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Connectivity/EdgeConnectivity.lean, line 187
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace SimpleGraph
variable {V : Type*} {G H : SimpleGraph V} {k l : ℕ∞} {u v w x y : V}
variable (G k u v) in
variable (G k) in

theorem isEdgeConnected_top_iff_forall_nat :
    G.IsEdgeConnected ⊤ ↔ ∀ n : ℕ, G.IsEdgeConnected n := by
  simp only [isEdgeConnected_iff]
  constructor
  · intro h n s hs
    exact h (hs.trans_le le_top)
  · intro h s hs
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hs.ne
    exact h (m + 1) (by rw [← hm]; exact_mod_cast Nat.lt_succ_self m)
