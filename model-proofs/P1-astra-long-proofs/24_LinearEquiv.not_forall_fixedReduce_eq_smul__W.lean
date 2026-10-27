/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     LinearEquiv.not_forall_fixedReduce_eq_smul
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Transvection/Generation.lean, line 349
             (added after the model's training data; human proof 42 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 4 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

private theorem not_forall_fixedReduce_eq_smul {f g : Dual K V} {v : V} {a b : K}
    (hv : LinearIndependent K
      ![e.fixedSubmodule.mkQ v, e.fixedReduce (e.fixedSubmodule.mkQ v)])
    {hf : e.fixedSubmodule ⊔ K ∙ (e v - v) ≤ LinearMap.ker f} (hfv : f v = 1)
    {hg : e.fixedSubmodule ⊔ K ∙ (e v - v) ≤ LinearMap.ker (f + g)} (hfgv : (f + g) v = 1)
    (hg0 : g ≠ 0) (hne_top : e.fixedSubmodule ⊔ K ∙ (e v - v) ⊔ K ∙ v < ⊤)
    (ha : ∀ x, (auxTransvection hf * e).fixedReduce x = a • x)
    (hb : ∀ x, (auxTransvection hg * e).fixedReduce x = b • x) :
    False := by
  classical
  let W : Submodule K V := e.fixedSubmodule ⊔ K ∙ v
  let S : Submodule K V := e.fixedSubmodule ⊔ K ∙ (e v - v) ⊔ K ∙ v
  have hWS : W ≤ S :=
    sup_le (le_trans le_sup_left le_sup_left) le_sup_right
  have hdS : e v - v ∈ S :=
    mem_sup_left (mem_sup_right (mem_span_singleton_self _))
  have hev : e v ∉ W := by
    intro hv'
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hv'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hy0 : e.fixedSubmodule.mkQ y = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact hy
    have hc0 : c • e.fixedSubmodule.mkQ v = e.fixedSubmodule.mkQ (e v) := by
      simpa only [map_add, _root_.map_smul, hy0, zero_add]
        using congrArg e.fixedSubmodule.mkQ hyz
    have hc : c • e.fixedSubmodule.mkQ v =
        e.fixedReduce (e.fixedSubmodule.mkQ v) := by
      simpa only [fixedReduce_mk, Submodule.mkQ_apply] using hc0
    have hi := (LinearIndependent.pair_iff.mp hv) (-c) 1 (by
      rw [← hc]
      simp)
    exact one_ne_zero hi.2
  have hA (x : V) : (auxTransvection hf * e) x - a • x ∈ W := by
    change (auxTransvection hf * e) x - a • x ∈ e.fixedSubmodule ⊔ K ∙ v
    rw [← auxTransvection_mul_fixed (hf := hf) hfv]
    rw [← (auxTransvection hf * e).fixedSubmodule.ker_mkQ,
      LinearMap.mem_ker, map_sub, sub_eq_zero]
    have hx := ha ((auxTransvection hf * e).fixedSubmodule.mkQ x)
    simp only [Submodule.mkQ_apply, fixedReduce_mk] at hx
    simpa only [_root_.map_smul, Submodule.mkQ_apply] using hx
  have hB (x : V) : (auxTransvection hg * e) x - b • x ∈ W := by
    change (auxTransvection hg * e) x - b • x ∈ e.fixedSubmodule ⊔ K ∙ v
    rw [← auxTransvection_mul_fixed (hf := hg) hfgv]
    rw [← (auxTransvection hg * e).fixedSubmodule.ker_mkQ,
      LinearMap.mem_ker, map_sub, sub_eq_zero]
    have hx := hb ((auxTransvection hg * e).fixedSubmodule.mkQ x)
    simp only [Submodule.mkQ_apply, fixedReduce_mk] at hx
    simpa only [_root_.map_smul, Submodule.mkQ_apply] using hx
  have hkey (x : V) : g (e x) • (e v - v) + (b - a) • x ∈ W := by
    convert W.sub_mem (hA x) (hB x) using 1 <;>
      simp only [auxTransvection, LinearEquiv.mul_apply, transvection.apply,
        LinearMap.add_apply, add_smul, sub_smul, smul_sub] <;> abel
  obtain ⟨x, hx⟩ : ∃ x : V, x ∉ S := by
    by_contra! hall
    exact (ne_of_lt hne_top) (Submodule.eq_top_iff'.mpr hall)
  have hba : b - a = 0 := by
    by_contra hba
    have hm : (b - a) • x ∈ S := by
      have := S.sub_mem (hWS (hkey x)) (S.smul_mem (g (e x)) hdS)
      simpa only [add_sub_cancel_left] using this
    apply hx
    have := S.smul_mem (b - a)⁻¹ hm
    simpa only [smul_smul, inv_mul_cancel₀ hba, one_smul] using this
  apply hg0
  apply LinearMap.ext
  intro y
  change g y = 0
  by_contra hgy
  have hm : g y • (e v - v) ∈ W := by
    simpa only [e.apply_symm_apply, hba, zero_smul, add_zero]
      using hkey (e.symm y)
  have hd : e v - v ∈ W := by
    have := W.smul_mem (g y)⁻¹ hm
    simpa only [smul_smul, inv_mul_cancel₀ hgy, one_smul] using this
  apply hev
  have := W.add_mem hd (mem_sup_right (mem_span_singleton_self v))
  simpa only [sub_add_cancel] using this
