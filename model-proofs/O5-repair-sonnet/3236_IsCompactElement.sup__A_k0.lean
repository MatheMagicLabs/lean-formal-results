/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsCompactElement.sup
Source:      Mathlib @ a02a63c2, Mathlib/Order/CompactlyGenerated/Basic.lean, line 97
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp, grind .]
protected theorem IsCompactElement.sup [SemilatticeSup α] {a b : α} (ha : IsCompactElement a)
    (hb : IsCompactElement b) : IsCompactElement (a ⊔ b) := by
  intro s u hne hdir hlub hle
  obtain ⟨x, hx, hax⟩ := ha s u hne hdir hlub (le_sup_left.trans hle)
  obtain ⟨y, hy, hby⟩ := hb s u hne hdir hlub (le_sup_right.trans hle)
  obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
  exact ⟨z, hz, sup_le (hax.trans hxz) (hby.trans hyz)⟩
