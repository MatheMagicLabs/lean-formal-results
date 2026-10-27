/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.associated_content_mul
Source:      Mathlib @ d0a050ad6, Mathlib/RingTheory/Polynomial/Content.lean, line 321
             (added after the model's training data; human proof 32 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 1 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem associated_content_mul (p q : R[X]) :
    Associated ((p * q).content) (p.content * q.content) := by
  suffices H : ∀ n (p q : R[X]), p.natDegree + q.natDegree = n →
      Associated (p * q).content (p.content * q.content) by
  { exact H _ p q rfl }
  intro n
  induction n using Nat.strong_induction_on
  rename_i n ih
  intro p q hn
  have hleft : ∀ a b : R[X], a.natDegree + b.natDegree = n →
      a.IsPrimitive → b.IsPrimitive →
      gcd (a * b).content a.leadingCoeff ∣ 1 := by
  {
  intro a b hab ha hb
  have hp : Associated (a.eraseLead * b).content a.eraseLead.content := by
  {
  by_cases hz : a.eraseLead = 0
  · simp [hz]
  have he := a.eraseLead_natDegree_lt_or_eraseLead_eq_zero.resolve_right hz
  have hlt : a.eraseLead.natDegree + b.natDegree < n := by
  { rw [← hab]; exact Nat.add_lt_add_right he _ }
  simpa only [hb.content_eq_one, mul_one] using
      ih _ hlt a.eraseLead b rfl
  }
  have hd : (a * b).content ∣ (a * b).eraseLead.content := by
  {
  rw [content_eq_gcd_leadingCoeff_content_eraseLead (a * b)]
  exact gcd_dvd_right _ _
  }
  have hh := gcd_dvd_gcd hd (dvd_refl a.leadingCoeff)
  rw [content_mul_aux, hp.gcd_eq_left, gcd_comm a.eraseLead.content,
      ← content_eq_gcd_leadingCoeff_content_eraseLead, ha.content_eq_one] at hh
  exact hh
  }
  have hcore : ∀ a b : R[X], a.natDegree + b.natDegree = n →
      a.IsPrimitive → b.IsPrimitive → (a * b).content = 1 := by
  {
  intro a b hab ha hb
  have h₁ := hleft a b hab ha hb
  have h₂ := hleft b a (by simpa only [Nat.add_comm] using hab) hb ha
  rw [mul_comm b a] at h₂
  have hd : (a * b).content ∣ a.leadingCoeff * b.leadingCoeff := by
  {
  rw [← leadingCoeff_mul]
  exact content_dvd_coeff _
  }
  have hb' : (a * b).content ∣ b.leadingCoeff :=
      (dvd_gcd_mul_of_dvd_mul hd).trans
        (by simpa only [one_mul] using mul_dvd_mul h₁ (dvd_refl b.leadingCoeff))
  have hu : (a * b).content ∣ 1 :=
      (dvd_gcd dvd_rfl hb').trans h₂
  exact dvd_antisymm_of_normalize_eq normalize_content normalize_one hu (one_dvd _)
  }
  have hprim : (p.primPart * q.primPart).content = 1 :=
      hcore _ _ (by simpa only [natDegree_primPart] using hn)
        p.isPrimitive_primPart q.isPrimitive_primPart
  have hf : p * q =
      C (p.content * q.content) * (p.primPart * q.primPart) := by
  {
  calc
  p * q = (C p.content * p.primPart) * (C q.content * q.primPart) :=
      congrArg₂ (fun a b : R[X] => a * b)
        p.eq_C_content_mul_primPart q.eq_C_content_mul_primPart
  _ = C (p.content * q.content) * (p.primPart * q.primPart) := by
      rw [map_mul]; ring
  }
  rw [hf]
  simpa only [hprim, mul_one] using
      associated_content_C_mul (p.content * q.content) (p.primPart * q.primPart)
