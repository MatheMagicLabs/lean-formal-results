/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ValueDistribution.isBigO_characteristic_sub_characteristic_moebius
Source:      Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/ValueDistribution/FirstMainTheorem.lean, line 202
             (added after the model's training data; human proof 46 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 9 call(s)
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
  classical
  change (characteristic f ⊤ - characteristic (fun z ↦ (a * f z + b) / (c * f z + d)) ⊤) =O[atTop] (1 : ℝ → ℝ)
  have hmul (g : ℂ → ℂ) (hg : Meromorphic g) (u : ℂ) (hu : u ≠ 0) :
      (characteristic g ⊤ - characteristic (fun z ↦ u * g z) ⊤) =O[atTop] (1 : ℝ → ℝ) := by
    first
    | exact isBigO_characteristic_sub_characteristic_const_mul hg hu
    | exact isBigO_characteristic_sub_characteristic_mul_const hg hu
    | simpa only [smul_eq_mul] using isBigO_characteristic_sub_characteristic_smul hg hu
  have hconst (u v : ℂ) :
      (characteristic (fun _ : ℂ ↦ u) ⊤ - characteristic (fun _ : ℂ ↦ v) ⊤) =O[atTop] (1 : ℝ → ℝ) := by
    apply isBigO_of_le' (c := |log⁺ ‖u‖ - log⁺ ‖v‖|)
    intro r
    simp [characteristic_const]
  by_cases hc : c = 0
  · have ha : a ≠ 0 := by
      intro ha
      simp [ha, hc] at hΔ
    have hd : d ≠ 0 := by
      intro hd
      simp [hd, hc] at hΔ
    have h₁ := hmul f hf (a / d) (div_ne_zero ha hd)
    have h₂ := isBigO_characteristic_sub_characteristic_shift
      (a₀ := -(b / d)) (show Meromorphic (fun z ↦ a / d * f z) by fun_prop)
    have heq :
        (fun z ↦ a / d * f z - -(b / d)) =
          (fun z ↦ (a * f z + b) / (c * f z + d)) := by
      funext z
      simp only [hc, zero_mul, zero_add, sub_neg_eq_add]
      ring
    rw [← heq]
    exact transitivity₁ _ h₂ h₁
  · let g : ℂ → ℂ := fun z ↦ c * f z + d
    have hg : Meromorphic g := by
      dsimp [g]
      fun_prop
    have hopen (P : ℂ → Prop) :
        IsOpen {x | ∀ᶠ y in nhdsWithin x ({x}ᶜ), P y} := by
      apply isOpen_iff_mem_nhds.mpr
      intro x hx
      change (∀ᶠ y in nhdsWithin x ({x}ᶜ), P y) at hx
      have hx' : ∀ᶠ y in nhds x, y ≠ x → P y := by
        simpa only [eventually_nhdsWithin_iff, Set.mem_compl_iff,
          Set.mem_singleton_iff] using hx
      obtain ⟨s, hs, hso, hxs⟩ := _root_.mem_nhds_iff.mp hx'
      apply Filter.mem_of_superset (hso.mem_nhds hxs)
      intro y hy
      by_cases hyx : y = x
      · subst y
        exact hx
      · have hy' : ∀ᶠ z in nhds y, P z := by
          filter_upwards [hso.mem_nhds hy,
            isClosed_singleton.isOpen_compl.mem_nhds hyx] with z hzs hzx
          exact hs hzs hzx
        exact hy'.filter_mono nhdsWithin_le_nhds
    have hlocal (x : ℂ) :
        (∀ᶠ y in nhdsWithin x ({x}ᶜ), g y = 0) ∨
          (∀ᶠ y in nhdsWithin x ({x}ᶜ), g y ≠ 0) := by
      first
      | simpa using (hg x).eventually_eq_zero_or_eventually_ne_zero
      | simpa using (hg x).eventually_eq_zero_or_ne_zero
      | simpa using (hg x).eventuallyEq_zero_or_eventually_ne_zero
      | simpa using (hg x).eventuallyEq_zero_or_ne_zero
    let A : Set ℂ := {x | ∀ᶠ y in nhdsWithin x ({x}ᶜ), g y = 0}
    let B : Set ℂ := {x | ∀ᶠ y in nhdsWithin x ({x}ᶜ), g y ≠ 0}
    have hAB : B = Aᶜ := by
      ext x
      constructor
      · intro hb ha
        change (∀ᶠ y in nhdsWithin x ({x}ᶜ), g y = 0) at ha
        change (∀ᶠ y in nhdsWithin x ({x}ᶜ), g y ≠ 0) at hb
        obtain ⟨y, hy₁, hy₂⟩ := (ha.and hb).exists
        exact hy₂ hy₁
      · intro ha
        rcases hlocal x with hx | hx
        · exact (ha hx).elim
        · exact hx
    have hAo : IsOpen A := hopen _
    have hAc : IsClosed A := by
      apply isOpen_compl_iff.mp
      rw [← hAB]
      exact hopen _
    have hAcl : IsClopen A := by
      constructor <;> first | exact hAo | exact hAc
    have htriv : A = ∅ ∨ A = Set.univ := by
      first
      | exact isClopen_iff.mp hAcl
      | exact isClopen_iff_eq_empty_or_univ.mp hAcl
    have hdiff (x : ℂ) : (Set.univ \ {x} : Set ℂ) = {x}ᶜ := by
      ext y
      simp
    have hcases :
        g =ᶠ[codiscrete ℂ] 0 ∨ ∀ᶠ z in codiscrete ℂ, g z ≠ 0 := by
      rcases htriv with hA | hA
      · right
        have hall : ∀ x : ℂ, ∀ᶠ y in nhdsWithin x ({x}ᶜ), g y ≠ 0 := by
          intro x
          have hx : x ∈ B := by
            rw [hAB, hA]
            simp
          exact hx
        simpa [Filter.Eventually, codiscrete, codiscreteWithin, hdiff] using hall
      · left
        have hall : ∀ x : ℂ, ∀ᶠ y in nhdsWithin x ({x}ᶜ), g y = 0 := by
          intro x
          have hx : x ∈ A := by rw [hA]; trivial
          exact hx
        simpa [Filter.EventuallyEq, Filter.Eventually, codiscrete,
          codiscreteWithin, hdiff] using hall
    rcases hcases with hz | hn
    · have heq : f =ᶠ[codiscrete ℂ] (fun _ ↦ -d / c) := by
        filter_upwards [hz] with z hz
        change c * f z + d = 0 at hz
        apply (eq_div_iff hc).2
        linear_combination hz
      have hq :
          (fun z ↦ (a * f z + b) / (c * f z + d)) =ᶠ[codiscrete ℂ] (fun _ ↦ 0) := by
        filter_upwards [hz] with z hz
        change c * f z + d = 0 at hz
        simp [hz]
      apply EventuallyEq.trans_isBigO _ (hconst (-d / c) 0)
      filter_upwards [Ioi_mem_atTop (0 : ℝ)] with r hr
      change characteristic f ⊤ r -
          characteristic (fun z ↦ (a * f z + b) / (c * f z + d)) ⊤ r =
        characteristic (fun _ : ℂ ↦ -d / c) ⊤ r -
          characteristic (fun _ : ℂ ↦ 0) ⊤ r
      rw [characteristic_congr_codiscrete heq (ne_of_gt hr),
        characteristic_congr_codiscrete hq (ne_of_gt hr)]
    · let k : ℂ := (b * c - a * d) / c
      have hk : k ≠ 0 := by
        dsimp [k]
        apply div_ne_zero _ hc
        intro hk
        apply hΔ
        linear_combination -hk
      have h₁ := hmul f hf c hc
      have h₂ := isBigO_characteristic_sub_characteristic_shift
        (a₀ := -d) (show Meromorphic (fun z ↦ c * f z) by fun_prop)
      have hfg :
          (characteristic f ⊤ - characteristic g ⊤) =O[atTop] (1 : ℝ → ℝ) := by
        simpa [g] using transitivity₁ _ h₂ h₁
      have h₃ := isBigO_characteristic_sub_characteristic_inv hg
      have h₄ := hmul g⁻¹ (by fun_prop) k hk
      have h₅ := isBigO_characteristic_sub_characteristic_shift
        (a₀ := -(a / c)) (show Meromorphic (fun z ↦ k * g⁻¹ z) by fun_prop)
      apply transitivity₂ (f₂ := fun z ↦ k * g⁻¹ z - -(a / c))
      · filter_upwards [hn] with z hz
        dsimp [g, k] at hz ⊢
        simp only [Pi.inv_apply, sub_neg_eq_add]
        field_simp
        <;> ring
      · exact transitivity₁ _ h₅
          (transitivity₁ _ h₄ (transitivity₁ _ h₃ hfg))
