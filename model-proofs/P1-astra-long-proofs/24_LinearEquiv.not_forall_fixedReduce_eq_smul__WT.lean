/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     LinearEquiv.not_forall_fixedReduce_eq_smul
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Transvection/Generation.lean, line 349
             (added after the model's training data; human proof 42 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 4 call(s)
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
  let W := e.fixedSubmodule ⊔ K ∙ v
  let U := e.fixedSubmodule ⊔ K ∙ (e v - v) ⊔ K ∙ v
  have hWU : W ≤ U := sup_le (le_trans le_sup_left le_sup_left) le_sup_right
  have hdU : v - e v ∈ U := by simpa only [neg_sub] using U.neg_mem (show e v - v ∈ U from mem_sup_left (mem_sup_right (mem_span_singleton_self _)))
  have ha' : ∀ x, e x + f (e x) • (v - e v) - a • x ∈ W := by have ht := (fixedReduce_eq_smul_iff (auxTransvection hf * e) a).mp ha; rw [auxTransvection_mul_fixed hfv] at ht; simpa only [auxTransvection, LinearEquiv.mul_apply, transvection.apply] using ht
  have hb' : ∀ x, e x + (f (e x) + g (e x)) • (v - e v) - b • x ∈ W := by have ht := (fixedReduce_eq_smul_iff (auxTransvection hg * e) b).mp hb; rw [auxTransvection_mul_fixed hfgv] at ht; simpa only [auxTransvection, LinearEquiv.mul_apply, transvection.apply, LinearMap.add_apply] using ht
  have haU : ∀ x, e x - a • x ∈ U := by intro x; convert U.sub_mem (hWU (ha' x)) (U.smul_mem (f (e x)) hdU) using 1 <;> abel
  have hbU : ∀ x, e x - b • x ∈ U := by intro x; convert U.sub_mem (hWU (hb' x)) (U.smul_mem (f (e x) + g (e x)) hdU) using 1 <;> abel
  have habU : ∀ x, (a - b) • x ∈ U := by intro x; convert U.sub_mem (hbU x) (haU x) using 1 <;> simp only [sub_smul] <;> abel
  have hab : a = b := by by_contra h; have ht : U = ⊤ := Submodule.eq_top_iff'.mpr (fun x ↦ (U.smul_mem_iff (sub_ne_zero.mpr h)).mp (habU x)); exact hne_top.ne ht
  have hdW : v - e v ∉ W := by intro hd; obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hd; obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz; have heq : (1 - c) • v + (-1 : K) • e v = y := (by convert (eq_sub_iff_add_eq.mpr hyz).symm using 1 <;> simp only [sub_smul, one_smul, neg_smul] <;> abel); have hzero : e.fixedSubmodule.mkQ y = 0 := (by rwa [← LinearMap.mem_ker, Submodule.ker_mkQ]); have hrel : (1 - c) • e.fixedSubmodule.mkQ v + (-1 : K) • e.fixedReduce (e.fixedSubmodule.mkQ v) = 0 := (by rw [fixedReduce_mkQ, ← LinearMap.map_smul, ← LinearMap.map_smul, ← map_add, heq, hzero]); exact (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0)) (((LinearIndependent.pair_iff.mp hv) (1 - c) (-1) hrel).2)
  have hgW : ∀ x, g (e x) • (v - e v) ∈ W := by intro x; convert W.sub_mem (hb' x) (ha' x) using 1 <;> rw [hab] <;> simp only [add_smul] <;> abel
  apply hg0
  ext x
  change g x = 0
  by_contra hx
  apply hdW
  apply (W.smul_mem_iff hx).mp
  simpa only [e.apply_symm_apply] using hgW (e.symm x)
