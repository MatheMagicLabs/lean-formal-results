/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MonotoneOn.eventually_le_two_mul'
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Function/BorelGrowth.lean, line 52
             (added after the model's training data; human proof 53 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 3 call(s)
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
  let E : Set ℝ := {r | a ≤ r ∧ 2 * S r < S (r + (S r)⁻¹)}
  let D : ℕ → Set ℝ := fun n => {r | r ∈ E ∧ (2 : ℝ) ^ n * S a ≤ S r ∧ S r < (2 : ℝ) ^ (n + 1) * S a}
  let R : ℕ → ℝ := fun n => ((2 : ℝ) ^ n * S a)⁻¹
  have hp (n : ℕ) : 0 < (2 : ℝ) ^ n * S a := mul_pos (pow_pos (by norm_num) _) h₂
  have hR (n : ℕ) : 0 ≤ R n := (inv_pos.mpr (hp n)).le
  have hstep (n : ℕ) (x y : ℝ) (hx : x ∈ D n) (hy : y ∈ D n) (hxy : x ≤ y) : y - x ≤ R n := by
  { have hxpos : 0 < S x := lt_of_lt_of_le (hp n) hx.2.1
    have hxshift : a ≤ x + (S x)⁻¹ := le_trans hx.1.1 (le_add_of_nonneg_right (inv_nonneg.mpr hxpos.le))
    have hhigh : (2 : ℝ) ^ (n + 1) * S a ≤ 2 * S x := by { rw [pow_succ]; nlinarith only [hx.2.1] }
    have hlt : y < x + (S x)⁻¹ := by { by_contra h; have hm := h₁ hxshift hy.1.1 (le_of_not_gt h); have hb := hx.1.2; have hu := hy.2.2; linarith }
    have hinv : (S x)⁻¹ ≤ R n := by { simpa only [one_div, R] using one_div_le_one_div_of_le (hp n) hx.2.1 }
    linarith }
  let c : ℕ → ℝ := fun n => if h : (D n).Nonempty then h.choose else 0
  have hc (n : ℕ) (h : (D n).Nonempty) : c n ∈ D n := by { dsimp only [c]; rw [dif_pos h]; exact h.choose_spec }
  have hinterval (n : ℕ) (x : ℝ) (hx : x ∈ D n) : x ∈ Icc (c n - R n) (c n + R n) := by
  { have hcn := hc n ⟨x, hx⟩
    exact (le_total x (c n)).elim (fun h => by { have hb := hstep n x (c n) hx hcn h; have hr := hR n; constructor <;> linarith }) (fun h => by { have hb := hstep n (c n) x hcn hx h; have hr := hR n; constructor <;> linarith }) }
  have hslices (r : ℝ) (hr : r ∈ E) : ∃ n, r ∈ D n := by
  { have hbase : S a ≤ S r := h₁ (le_refl a) hr.1 hr.1
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (S r / S a) (by norm_num : (1 : ℝ) < 2)
    have hex : ∃ m : ℕ, S r < (2 : ℝ) ^ m * S a := ⟨m, (div_lt_iff₀ h₂).mp hm⟩
    have hne : Nat.find hex ≠ 0 := by { intro hz; have hh := Nat.find_spec hex; rw [hz, pow_zero, one_mul] at hh; linarith }
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hne
    have hlo : (2 : ℝ) ^ n * S a ≤ S r := le_of_not_gt (Nat.find_min hex (by omega : n < Nat.find hex))
    have hhi := Nat.find_spec hex
    rw [hn] at hhi
    exact ⟨n, hr, hlo, hhi⟩ }
  have hcover : E ⊆ ⋃ n : ℕ, Icc (c n - R n) (c n + R n) := by { intro r hr; obtain ⟨n, hn⟩ := hslices r hr; exact mem_iUnion.mpr ⟨n, hinterval n r hn⟩ }
  have hsum : Summable (fun n : ℕ => 2 * R n) := by
  { have hg : Summable (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) := summable_geometric_of_abs_lt_one (by norm_num)
    convert hg.mul_left (2 * (S a)⁻¹) using 1
    ext n
    dsimp only [R]
    simp only [mul_inv_rev, inv_pow]
    ring }
  have hseries : (∑' n : ℕ, ENNReal.ofReal (2 * R n)) < ⊤ := by { rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (by norm_num) (hR n)) hsum]; exact ENNReal.ofReal_lt_top }
  have hvol (n : ℕ) : volume (Icc (c n - R n) (c n + R n)) = ENNReal.ofReal (2 * R n) := by { rw [Real.volume_Icc]; congr 1; ring }
  have hfinite : volume E < ⊤ := by
  { have hb : volume (⋃ n : ℕ, Icc (c n - R n) (c n + R n)) ≤ ∑' n : ℕ, volume (Icc (c n - R n) (c n + R n)) := measure_iUnion_le _
    simp only [hvol] at hb
    exact lt_of_le_of_lt ((measure_mono hcover).trans hb) hseries }
  have hset : {r | r ∉ E}ᶜ = E := by { ext r; simp only [mem_compl_iff, mem_setOf_eq, not_not] }
  have he : ∀ᶠ r in volume.cofinite, r ∉ E := by { change volume {r | r ∉ E}ᶜ < ⊤; rw [hset]; exact hfinite }
  have he' : ∀ᶠ r in volume.cofinite ⊓ atTop, r ∉ E := he.filter_mono inf_le_left
  have ha' : ∀ᶠ r in volume.cofinite ⊓ atTop, a ≤ r := (eventually_ge_atTop a).filter_mono inf_le_right
  filter_upwards [he', ha'] with r hr har
  exact le_of_not_gt (fun h => hr ⟨har, h⟩)
