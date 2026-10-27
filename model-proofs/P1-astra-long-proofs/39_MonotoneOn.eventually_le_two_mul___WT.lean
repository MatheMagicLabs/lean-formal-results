/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MonotoneOn.eventually_le_two_mul'
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Function/BorelGrowth.lean, line 52
             (added after the model's training data; human proof 53 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 2 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

private theorem MonotoneOn.eventually_le_two_mul' {S : ℝ → ℝ} {a : ℝ}
    (h₁ : MonotoneOn S (Set.Ici a)) (h₂ : 0 < S a) :
    ∀ᶠ r in volume.cofinite ⊓ atTop, S (r + (S r)⁻¹) ≤ 2 * S r := by
  classical
  let E : Set ℝ := {r | a ≤ r ∧ ¬ S (r + (S r)⁻¹) ≤ 2 * S r}
  let D : ℕ → Set ℝ := fun n => {r | a ≤ r ∧ ¬ S (r + (S r)⁻¹) ≤ 2 * S r ∧ 2 ^ n * S a ≤ S r ∧ S r < 2 ^ (n + 1) * S a}
  have hsep (n : ℕ) (x : ℝ) (hx : x ∈ D n) (y : ℝ) (hy : y ∈ D n) : y - x ≤ (2 ^ n * S a)⁻¹ := by
  {
  have hc : 0 < (2 : ℝ) ^ n * S a := mul_pos (pow_pos (by norm_num) _) h₂
  have hp : 0 < S x := hc.trans_le hx.2.2.1
  have ht : y < x + (S x)⁻¹ := by
  {
  by_contra hn
  have ha : a ≤ x + (S x)⁻¹ := le_trans hx.1 (le_add_of_nonneg_right (inv_nonneg.mpr hp.le))
  have hm := h₁ ha hy.1 (le_of_not_gt hn)
  have hb := lt_of_not_ge hx.2.1
  have hu := hy.2.2.2
  have hl := hx.2.2.1
  rw [pow_succ] at hu
  nlinarith
  }
  have hi := inv_anti₀ hc hx.2.2.1
  linarith
  }
  have hvol (n : ℕ) : volume (D n) ≤ ENNReal.ofReal ((2 ^ n * S a)⁻¹) := by
  {
  refine (Real.volume_le_diam _).trans (Metric.ediam_le_iff.mpr ?_)
  intro x hx y hy
  rw [edist_dist, Real.dist_eq]
  apply ENNReal.ofReal_le_ofReal
  apply abs_le.mpr
  constructor
  · have h := hsep n x hx y hy; linarith
  · have h := hsep n y hy x hx; linarith
  }
  have hcover : E ⊆ ⋃ n, D n := by
  {
  intro r hr
  have hs : S a ≤ S r := h₁ (le_refl a) hr.1 hr.1
  have hratio : 1 ≤ S r / S a := (le_div_iff₀ h₂).mpr (by simpa using hs)
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  exact mem_iUnion.mpr ⟨n, hr.1, hr.2, (le_div_iff₀ h₂).mp hn, (div_lt_iff₀ h₂).mp hn'⟩
  }
  have hsum : Summable (fun n : ℕ => ((2 : ℝ) ^ n * S a)⁻¹) := by
  {
  simpa only [mul_inv_rev, ← inv_pow, one_div, mul_comm] using summable_geometric_two.mul_right (S a)⁻¹
  }
  have hfinite : volume E < ⊤ := lt_of_le_of_lt ((measure_mono hcover).trans ((measure_iUnion_le D).trans (ENNReal.tsum_le_tsum hvol))) hsum.tsum_ofReal_lt_top
  refine eventually_inf.mpr ⟨Eᶜ, volume.compl_mem_cofinite.mpr hfinite, Ici a, Ici_mem_atTop a, ?_⟩
  intro r hr
  by_contra hn
  exact hr.1 ⟨hr.2, hn⟩
