/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Integral/IntervalIntegral/MeanValue.lean, line 115
             (added after the model's training data; human proof 44 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 8 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn
    (hab : a ≤ b) (hf : 0 ≤ f b) (hf_mon : AntitoneOn f (Icc a b))
    (hg : IntervalIntegrable g volume a b) :
    ∃ ξ ∈ Icc a b, ∫ x in a..b, f x * g x = f a * ∫ x in a..ξ, g x := by
  classical
  have hne (z : ℝ) : ∀ᵐ x : ℝ ∂volume, x ≠ z := by {
  rw [ae_iff]
  simp
  }
  have hfa : 0 ≤ f a := hf.trans (hf_mon ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  let w : ℝ → ℝ := fun x => f (max a (min b x))
  have hclamp (x : ℝ) : max a (min b x) ∈ Icc a b := ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hw : Antitone w := by {
  intro x y hxy
  exact hf_mon (hclamp x) (hclamp y) (max_le_max_left a (min_le_min_left b hxy))
  }
  have hw_eq (x : ℝ) (hx : x ∈ Icc a b) : w x = f x := by {
  simp only [w, min_eq_right hx.2, max_eq_right hx.1]
  }
  have hw0 (x : ℝ) : 0 ≤ w x := hf.trans (hf_mon (hclamp x) ⟨hab, le_rfl⟩ (hclamp x).2)
  have hwa (x : ℝ) : w x ≤ f a := hf_mon ⟨le_rfl, hab⟩ (hclamp x) (hclamp x).1
  let g₀ : ℝ → ℝ := (Ioc a b).indicator g
  have hg₀ : Integrable g₀ volume := by {
  exact (integrable_indicator_iff measurableSet_Ioc).mpr hg.1
  }
  let ν : Measure ℝ := volume.restrict (Ioc 0 (f a))
  haveI : IsFiniteMeasure ν := ⟨by simp [ν, Real.volume_Ioc]⟩
  let K : ℝ → ℝ → ℝ := fun t x => if t ≤ w x then g₀ x else 0
  have hKm : AEStronglyMeasurable (fun p : ℝ × ℝ => K p.1 p.2) (ν.prod volume) := by {
  exact hg₀.aestronglyMeasurable.comp_snd.indicator (measurableSet_le measurable_fst (hw.measurable.comp measurable_snd))
  }
  have hKd : Integrable (fun p : ℝ × ℝ => (1 : ℝ) * ‖g₀ p.2‖) (ν.prod volume) := Integrable.mul_prod (integrable_const (1 : ℝ)) hg₀.norm
  have hK : Integrable (fun p : ℝ × ℝ => K p.1 p.2) (ν.prod volume) := by {
  apply hKd.mono' hKm
  filter_upwards [] with p
  dsimp [K]
  split_ifs <;> simp
  }
  have hKt (x : ℝ) : (∫ t, K t x ∂ν) = w x * g₀ x := by {
  change (∫ t, (Iic (w x)).indicator (fun _ : ℝ => g₀ x) t ∂ν) = _
  rw [MeasureTheory.integral_indicator measurableSet_Iic]
  have hm : ν.restrict (Iic (w x)) = volume.restrict (Ioc 0 (w x)) := by {
  dsimp [ν]
  rw [Measure.restrict_restrict measurableSet_Iic]
  congr 1
  ext t
  simp only [mem_inter_iff, mem_Iic, mem_Ioc]
  constructor
  · {
  intro ht
  exact ⟨ht.2.1, ht.1⟩
  }
  · {
  intro ht
  exact ⟨ht.2, ht.1, ht.2.trans (hwa x)⟩
  }
  }
  rw [hm]
  simp [MeasureTheory.integral_const, Measure.real, Real.volume_Ioc, hw0 x, smul_eq_mul]
  }
  have hweight : (∫ x, w x * g₀ x) = ∫ x in a..b, f x * g x := by {
  rw [intervalIntegral.integral_of_le hab]
  have heq : (∫ x, w x * g₀ x) = ∫ x, (Ioc a b).indicator (fun x => f x * g x) x := by {
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Ioc a b
  · { simp [g₀, hx, hw_eq x ⟨hx.1.le, hx.2⟩] }
  · { simp [g₀, hx] }
  }
  rw [heq, MeasureTheory.integral_indicator measurableSet_Ioc]
  }
  have hswap : (∫ t, ∫ x, K t x ∂volume ∂ν) = ∫ x, ∫ t, K t x ∂ν ∂volume := by {
  exact MeasureTheory.integral_integral_swap hK
  }
  have htotal : (∫ t, ∫ x, K t x ∂volume ∂ν) = ∫ x in a..b, f x * g x := by {
  rw [hswap]
  exact (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hKt)).trans hweight
  }
  let H : ℝ → ℝ := fun x => ∫ y in a..x, g y
  have hgcc : IntegrableOn g (uIcc a b) volume := by {
  rw [uIcc_of_le hab]
  change Integrable g (volume.restrict (Icc a b))
  apply (hg₀.integrableOn : Integrable g₀ (volume.restrict (Icc a b))).congr
  filter_upwards [ae_restrict_of_ae (hne a), ae_restrict_mem measurableSet_Icc] with x hxa hx
  have hx' : x ∈ Ioc a b := ⟨lt_of_le_of_ne hx.1 hxa.symm, hx.2⟩
  exact indicator_of_mem hx' g
  }
  have hH : ContinuousOn H (Icc a b) := by {
  simpa only [H, uIcc_of_le hab] using intervalIntegral.continuousOn_primitive_interval hgcc
  }
  have hcut (t : ℝ) : ∃ c ∈ Icc a b, (∫ x, K t x) = H c := by {
  let S : Set ℝ := insert a {x | x ∈ Icc a b ∧ t ≤ w x}
  have hSne : S.Nonempty := ⟨a, Or.inl rfl⟩
  have hSupper : ∀ x ∈ S, x ≤ b := by {
  rintro x (rfl | hx)
  · { exact hab }
  · { exact hx.1.2 }
  }
  have hSb : BddAbove S := ⟨b, hSupper⟩
  let c := sSup S
  have hc : c ∈ Icc a b := ⟨le_csSup hSb (Or.inl rfl), csSup_le hSne hSupper⟩
  have hlower (x : ℝ) (hax : a < x) (hxc : x < c) : t ≤ w x := by {
  have hex : ∃ y ∈ S, x < y := by {
  by_contra hn
  have hle : c ≤ x := by {
  apply csSup_le hSne
  intro y hy
  exact le_of_not_gt (fun hxy => hn ⟨y, hy, hxy⟩)
  }
  exact (not_le_of_gt hxc) hle
  }
  obtain ⟨y, hy, hxy⟩ := hex
  change y = a ∨ (y ∈ Icc a b ∧ t ≤ w y) at hy
  rcases hy with rfl | hy
  · { exact (not_lt_of_ge hax.le hxy).elim }
  · { exact hy.2.trans (hw hxy.le) }
  }
  have heq : (fun x => K t x) =ᵐ[volume] (Ioc a c).indicator g := by {
  filter_upwards [hne c] with x hxc
  by_cases hxab : x ∈ Ioc a b
  · {
  by_cases hle : x ≤ c
  · {
  have hac : x ∈ Ioc a c := ⟨hxab.1, hle⟩
  have ht : t ≤ w x := hlower x hxab.1 (lt_of_le_of_ne hle hxc)
  simp [K, g₀, hxab, hac, ht]
  }
  · {
  have hac : x ∉ Ioc a c := fun hx => hle hx.2
  have ht : ¬t ≤ w x := by {
  intro ht
  exact hle (le_csSup hSb (Or.inr ⟨⟨hxab.1.le, hxab.2⟩, ht⟩))
  }
  simp [K, g₀, hxab, hac, ht]
  }
  }
  · {
  have hac : x ∉ Ioc a c := by {
  intro hx
  exact hxab ⟨hx.1, hx.2.trans hc.2⟩
  }
  simp [K, g₀, hxab, hac]
  }
  }
  refine ⟨c, hc, ?_⟩
  rw [MeasureTheory.integral_congr_ae heq, MeasureTheory.integral_indicator measurableSet_Ioc]
  exact (intervalIntegral.integral_of_le hc.1).symm
  }
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a, ⟨le_rfl, hab⟩⟩ hH
  obtain ⟨v, hv, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, ⟨le_rfl, hab⟩⟩ hH
  have h_integrable : Integrable (fun t => ∫ x, K t x) ν := hK.integral_prod_left
  have hconst (r : ℝ) : (∫ _ : ℝ, r ∂ν) = f a * r := by {
  simp [ν, MeasureTheory.integral_const, Measure.real, Real.volume_Ioc, hfa, smul_eq_mul]
  }
  have hlo : f a * H u ≤ ∫ x in a..b, f x * g x := by {
  rw [← hconst (H u), ← htotal]
  apply MeasureTheory.integral_mono_ae (integrable_const _) h_integrable
  filter_upwards [] with t
  obtain ⟨c, hc, heq⟩ := hcut t
  rw [heq]
  exact hmin hc
  }
  have hhi : (∫ x in a..b, f x * g x) ≤ f a * H v := by {
  rw [← hconst (H v), ← htotal]
  apply MeasureTheory.integral_mono_ae h_integrable (integrable_const _)
  filter_upwards [] with t
  obtain ⟨c, hc, heq⟩ := hcut t
  rw [heq]
  exact hmax hc
  }
  have hp : IsPreconnected ((fun x => f a * H x) '' Icc a b) := isPreconnected_Icc.image _ (continuousOn_const.mul hH)
  have hmem : (∫ x in a..b, f x * g x) ∈ (fun x => f a * H x) '' Icc a b := hp.ordConnected.out ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ ⟨hlo, hhi⟩
  obtain ⟨ξ, hξ, heq⟩ := hmem
  exact ⟨ξ, hξ, heq.symm⟩
