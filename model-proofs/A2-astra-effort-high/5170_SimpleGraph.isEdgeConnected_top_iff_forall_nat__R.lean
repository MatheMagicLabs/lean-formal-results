/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.isEdgeConnected_top_iff_forall_nat
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Connectivity/EdgeConnectivity.lean, line 187
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace SimpleGraph
variable {V : Type*} {G H : SimpleGraph V} {k l : ℕ∞} {u v w x y : V}
variable (G k u v) in
variable (G k) in

theorem isEdgeConnected_top_iff_forall_nat :
    G.IsEdgeConnected ⊤ ↔ ∀ n : ℕ, G.IsEdgeConnected n := by
  simp only [IsEdgeConnected, isEdgeReachable_top_iff_forall_nat]
  constructor
  · intro h n u v
    exact h u v n
  · intro h u v n
    exact h n u v
