/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Integral/IntervalIntegral/MeanValue.lean, line 115
             (added after the model's training data; human proof 44 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 5 call(s)
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
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hfa : 0 ≤ f a := hf.trans (hf_mon ha hb hab)
  have hg' : IntegrableOn g (Icc a b) := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hg
  let F : ℝ → ℝ := fun x => f (max a (min b x))
  have hc : ∀ x : ℝ, max a (min b x) ∈ Icc a b := fun x => ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hF : Antitone F := by {
  intro x y hxy;
  exact hf_mon (hc x) (hc y) (max_le_max le_rfl (min_le_min le_rfl hxy)) }
  have hFeq : ∀ x ∈ Icc a b, F x = f x := by {
  intro x hx;
  simp only [F, min_eq_right hx.2, max_eq_right hx.1] }
  have hF0 : ∀ x, 0 ≤ F x := fun x => hf.trans (hf_mon (hc x) hb (hc x).2)
  have hFA : ∀ x, F x ≤ f a := fun x => hf_mon ha (hc x) (hc x).1
  let K : ℝ × ℝ → ℝ := fun z => if z.2 < F z.1 then g z.1 else 0
  have hK : Integrable K ((volume.restrict (Icc a b)).prod (volume.restrict (Icc 0 (f a)))) := by {
  change Integrable ({z : ℝ × ℝ | z.2 < F z.1}.indicator (fun z => g z.1)) _;
  exact (hg'.comp_fst (volume.restrict (Icc 0 (f a)))).indicator (measurableSet_lt measurable_snd (hF.measurable.comp measurable_fst)) }
  let G : ℝ → ℝ := fun x => ∫ y in Icc a x, g y
  let H : ℝ → ℝ := fun t => ∫ x in Icc a b, K (x, t)
  have hG : ContinuousOn G (Icc a b) := continuousOn_primitive_Icc hg'
  have hH : ∀ t, ∃ c ∈ Icc a b, H t = G c := by {
  intro t;
  let S : Set ℝ := {x | x ∈ Icc a b ∧ t < F x};
  by_cases hS : S.Nonempty;
  · {
  have hbd : BddAbove S := ⟨b, fun x hx => hx.1.2⟩;
  let c := sSup S;
  have hcb : c ≤ b := csSup_le hS (fun x hx => hx.1.2);
  obtain ⟨z, hz⟩ := hS;
  have hac : a ≤ c := hz.1.1.trans (le_csSup hbd hz);
  have hSc : ∀ x ∈ Icc a b, x ≠ c → (t < F x ↔ x ≤ c) := by {
  intro x hx hxc;
  constructor;
  · { intro hxt; exact le_csSup hbd ⟨hx, hxt⟩ };
  · {
  intro hxc';
  obtain ⟨y, hy, hxy⟩ := exists_lt_of_lt_csSup ⟨z, hz⟩ (lt_of_le_of_ne hxc' hxc);
  exact hy.2.trans_le (hF hxy.le) } };
  refine ⟨c, ⟨hac, hcb⟩, ?_⟩;
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ c := by { rw [ae_iff]; simp };
  calc
  H t = ∫ x in Icc a b, (Icc a c).indicator g x := by {
  apply MeasureTheory.integral_congr_ae;
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with x hx hxc;
  have he : (t < F x) ↔ x ∈ Icc a c := by {
  rw [hSc x hx hxc];
  exact ⟨fun h => ⟨hx.1, h⟩, fun h => h.2⟩ };
  by_cases hp : t < F x;
  · { simp [K, hp, he.mp hp] };
  · { have hn : x ∉ Icc a c := fun hm => hp (he.mpr hm); simp [K, hp, hn] } }
  _ = G c := by {
  rw [setIntegral_indicator measurableSet_Icc];
  have he : Icc a b ∩ Icc a c = Icc a c := inter_eq_right.mpr (fun x hx => ⟨hx.1, hx.2.trans hcb⟩);
  rw [he] } };
  · {
  refine ⟨a, ha, ?_⟩;
  have he : H t = 0 := by {
  apply integral_eq_zero_of_ae;
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx;
  have hn : ¬t < F x := fun ht => hS ⟨x, hx, ht⟩;
  change (if t < F x then g x else 0) = 0;
  exact if_neg hn };
  simpa [G] using he } }
  have hinner : ∀ x ∈ Icc a b, (∫ t in Icc 0 (f a), K (x, t)) = f x * g x := by {
  intro x hx;
  change (∫ t in Icc 0 (f a), (Iio (F x)).indicator (fun _ => g x) t) = _;
  rw [setIntegral_indicator measurableSet_Iio];
  have he : Icc 0 (f a) ∩ Iio (F x) = Ico 0 (F x) := by {
  ext t;
  simp only [mem_inter_iff, mem_Icc, mem_Iio, mem_Ico];
  constructor;
  · { intro ht; exact ⟨ht.1.1, ht.2⟩ };
  · { intro ht; exact ⟨⟨ht.1, ht.2.le.trans (hFA x)⟩, ht.2⟩ } };
  rw [he, setIntegral_const, Real.volume_real_Ico_of_le (hF0 x)];
  simp only [sub_zero, smul_eq_mul, hFeq x hx] }
  have hrep : (∫ x in a..b, f x * g x) = ∫ t in Icc 0 (f a), H t := by {
  calc
  (∫ x in a..b, f x * g x) = ∫ x in Icc a b, f x * g x := by {
  rw [integral_Icc_eq_integral_Ioc, integral_of_le hab] }
  _ = ∫ x in Icc a b, ∫ t in Icc 0 (f a), K (x, t) := by {
  apply MeasureTheory.integral_congr_ae;
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx;
  exact (hinner x hx).symm }
  _ = ∫ t in Icc 0 (f a), H t := integral_integral_swap hK }
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a, ha⟩ hG
  obtain ⟨M, hM, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, ha⟩ hG
  have hlo : ∀ t, G m ≤ H t := by {
  intro t;
  obtain ⟨c, hc', he⟩ := hH t;
  rw [he];
  exact hmin hc' }
  have hhi : ∀ t, H t ≤ G M := by {
  intro t;
  obtain ⟨c, hc', he⟩ := hH t;
  rw [he];
  exact hmax hc' }
  have hHi : Integrable H (volume.restrict (Icc 0 (f a))) := hK.integral_prod_right
  have hlow : f a * G m ≤ ∫ t in Icc 0 (f a), H t := by {
  have h := MeasureTheory.integral_mono (integrable_const (G m)) hHi hlo;
  simpa only [setIntegral_const, Real.volume_real_Icc_of_le hfa, sub_zero, smul_eq_mul] using h }
  have hupp : (∫ t in Icc 0 (f a), H t) ≤ f a * G M := by {
  have h := MeasureTheory.integral_mono hHi (integrable_const (G M)) hhi;
  simpa only [setIntegral_const, Real.volume_real_Icc_of_le hfa, sub_zero, smul_eq_mul] using h }
  have hcont : ContinuousOn (fun x => f a * G x) (Icc a b) := continuousOn_const.mul hG
  obtain ⟨ξ, hξ, he⟩ := isPreconnected_Icc.intermediate_value hm hM hcont ⟨hlow, hupp⟩
  refine ⟨ξ, hξ, ?_⟩
  rw [hrep, ← he]
  change f a * (∫ x in Icc a ξ, g x) = f a * ∫ x in a..ξ, g x
  rw [integral_Icc_eq_integral_Ioc, integral_of_le hξ.1]
