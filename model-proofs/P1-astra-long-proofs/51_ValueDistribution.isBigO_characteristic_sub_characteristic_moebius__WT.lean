/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ValueDistribution.isBigO_characteristic_sub_characteristic_moebius
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/ValueDistribution/FirstMainTheorem.lean, line 202
             (added after the model's training data; human proof 46 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 2 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem isBigO_characteristic_sub_characteristic_moebius {a b c d : ℂ} {f : ℂ → ℂ}
    (hf : Meromorphic f) (hΔ : a * d - b * c ≠ 0) :
    (characteristic f ⊤ - characteristic ((a * f · + b) / (c * f · + d)) ⊤)
      =O[atTop] (1 : ℝ → ℝ) := by
  have H (g : ℂ → ℂ) (hg : Meromorphic g) (s t : ℂ) (hs : s ≠ 0) : (characteristic g ⊤ - characteristic (fun z ↦ s * g z + t) ⊤) =O[atTop] (1 : ℝ → ℝ) := by {
  apply transitivity₁ (fun z ↦ s * g z)
  · simpa only [sub_neg_eq_add] using (isBigO_characteristic_sub_characteristic_shift (f := fun z ↦ s * g z) (a₀ := -t) (by fun_prop))
  · have he : s • g = fun z ↦ s * g z := by { ext z; simp }
    rw [← he]
    exact isBigO_characteristic_sub_characteristic_const_mul hg hs }
  by_cases hc : c = 0
  · {
  have had : a * d ≠ 0 := by simpa [hc] using hΔ
  have ha : a ≠ 0 := (mul_ne_zero_iff.mp had).1
  have hd : d ≠ 0 := (mul_ne_zero_iff.mp had).2
  have he : ((a * f · + b) / (c * f · + d)) = (fun z ↦ (a / d) * f z + b / d) := by {
  ext z
  simp [hc, add_div, div_mul_eq_mul_div] }
  rw [he]
  exact H f hf (a / d) (b / d) (div_ne_zero ha hd) }
  let g : ℂ → ℂ := fun z ↦ c * f z + d
  have hg : Meromorphic g := by dsimp [g]; fun_prop
  have hfg : (characteristic f ⊤ - characteristic g⁻¹ ⊤) =O[atTop] (1 : ℝ → ℝ) := transitivity₁ g (isBigO_characteristic_sub_characteristic_inv hg) (H f hf c d hc)
  by_cases hz : ∃ z, meromorphicOrderAt g z = ⊤
  · {
  have he := hg.exists_meromorphicOrderAt_eq_top_iff_eventually_zero.mp hz
  apply transitivity₂ (f₂ := g⁻¹) _ hfg
  filter_upwards [he] with z hz
  change g z = 0 at hz
  change (g z)⁻¹ = (a * f z + b) / g z
  simp [hz] }
  have hn : ∀ z, meromorphicOrderAt g z ≠ ⊤ := by simpa only [not_exists] using hz
  have he : ∀ᶠ z in codiscrete ℂ, g z ≠ 0 := by {
  change ∀ᶠ z in codiscreteWithin Set.univ, g z ≠ 0
  exact hg.meromorphicOn.eventually_codiscreteWithin_apply_ne_zero (fun z _ ↦ hn z) }
  have hs : (b * c - a * d) / c ≠ 0 := by {
  apply div_ne_zero _ hc
  intro h
  apply hΔ
  linear_combination -h }
  have hi : Meromorphic g⁻¹ := by fun_prop
  apply transitivity₂ (f₂ := fun z ↦ ((b * c - a * d) / c) * g⁻¹ z + a / c)
  · {
  filter_upwards [he] with z hz
  change ((b * c - a * d) / c) * (g z)⁻¹ + a / c = (a * f z + b) / g z
  field_simp
  dsimp [g]
  ring }
  · exact transitivity₁ g⁻¹ (H g⁻¹ hi _ _ hs) hfg
