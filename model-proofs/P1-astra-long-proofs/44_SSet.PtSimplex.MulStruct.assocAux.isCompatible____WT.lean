/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SSet.PtSimplex.MulStruct.assocAux.isCompatible_α
Source:      Mathlib @ d0a050ad6, Mathlib/AlgebraicTopology/SimplicialSet/KanComplex/MulStruct.lean, line 363
             (added after the model's training data; human proof 45 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 10 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

private lemma isCompatible_α : horn.IsCompatible (fun j hj ↦ α h₀₂ h₁₃ h j hj) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hc (hh : i.castSucc.succ.succ ≠ Fin.last (n + 2)) :
      i.castSucc.succ.succ.castPred hh = i.succ.succ := by
    apply Fin.ext
    rfl
  have castPred_val (a : Fin (n + 3)) (ha : a ≠ Fin.last (n + 2)) :
      (a.castPred ha).val = a.val := rfl
  have cases (a : Fin (n + 3)) (ha : a ≠ i.castSucc.castSucc.succ) :
      a < i.castSucc.castSucc.castSucc ∨
      a = i.castSucc.castSucc.castSucc ∨
      a = i.castSucc.succ.succ ∨
      a = i.succ.succ.succ ∨
      i.succ.succ.succ < a := by
    grind
  rcases cases j hj with hj' | rfl | rfl | rfl | hj'
  all_goals rcases cases k hk with hk' | rfl | rfl | rfl | hk'
  all_goals clear cases
  all_goals try grind
  all_goals try have ej := α_of_lt h₀₂ h₁₃ h _ hj'
  all_goals try have ej := α_of_gt h₀₂ h₁₃ h _ hj'
  all_goals try have ek := α_of_lt h₀₂ h₁₃ h _ hk'
  all_goals try have ek := α_of_gt h₀₂ h₁₃ h _ hk'
  all_goals
    simp (disch := grind [castPred_val]) only [*,
      α_castSucc_castSucc_castSucc, α_castSucc_succ_succ,
      α_succ_succ_succ, Fin.pred_succ, Fin.castPred_castSucc,
      δ_castSucc_castSucc_map, δ_succ_castSucc_map, δ_succ_succ_map,
      δ_map_of_lt, δ_map_of_gt, comp_const]
  all_goals first
    | exact (h₁₃.δ_map_of_lt _ hj').symm
    | exact (h.δ_map_of_lt _ hj').symm
    | exact (h₀₂.δ_map_of_lt _ hj').symm
    | apply h₁₃.δ_map_of_gt
    | apply h.δ_map_of_gt
    | apply h₀₂.δ_map_of_gt
  all_goals
    change i.val + 2 < k.val - 1
    change i.val + 3 < k.val at hk'
    omega
