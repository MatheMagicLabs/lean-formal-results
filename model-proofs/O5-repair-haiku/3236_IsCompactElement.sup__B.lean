/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsCompactElement.sup
Source:      Mathlib @ a02a63c2, Mathlib/Order/CompactlyGenerated/Basic.lean, line 97
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-haiku, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-haiku-4-5
Setup:       Haiku 4.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp, grind .]
protected theorem IsCompactElement.sup [SemilatticeSup α] {a b : α} (ha : IsCompactElement a)
    (hb : IsCompactElement b) : IsCompactElement (a ⊔ b) := by
  intro s u hne hdir hlub hle
  have ha_le : a ≤ u := le_trans le_sup_left hle
  have hb_le : b ≤ u := le_trans le_sup_right hle
  obtain ⟨x, hxs, hax⟩ := ha s u hne hdir hlub ha_le
  obtain ⟨y, hys, hby⟩ := hb s u hne hdir hlub hb_le
  obtain ⟨z, hzs, hxz, hyz⟩ := hdir x hxs y hys
  exact ⟨z, hzs, sup_le (le_trans hax hxz) (le_trans hby hyz)⟩
