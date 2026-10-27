/-
Disproof of `rudins_conjecture_unique` from google-deepmind/formal-conjectures (commit 84cf7f8),
file FormalConjectures/Wikipedia/RudinsConjecture.lean, where the statement is listed as open.

Everything above the theorem at the end is the unchanged formal-conjectures file up to that
statement (Apache-2.0, (c) The Formal Conjectures Authors). The proof of the negation was written by
GPT-6 Astra during the F2 audit and checked by Lean v4.33.1 with Mathlib 0df444a; it depends only on
propext, Classical.choice and Quot.sound.
-/

/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Rudin's conjecture on squares in arithmetic progressions


*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Rudin%27s_conjecture)
- [Ru60] Rudin, W., *Trigonometric series with gaps*, J. Math. Mech. 9 (1960), 203–227.
- González-Jiménez, E. and Xarles, X., *On a conjecture of Rudin on squares in arithmetic
  progressions*, LMS J. Comput. Math. 17 (2014), 58–76.
-/

@[expose] public section

open Filter Asymptotics Real

namespace RudinsConjecture

/-- $Q(N; q, a)$ is the number of perfect squares among the first $N$ terms of the arithmetic
progression $\{q n + a : 0 \le n < N\}$. -/
noncomputable abbrev Q (N q a : ℕ) : ℕ := {n : ℕ | n < N ∧ IsSquare (q * n + a)}.ncard

/-- A pair $(q, a)$ describes a *non-trivial* arithmetic progression if $q, a \ge 1$,
$\gcd(q, a) = 1$, and $(q, a) \neq (1, 1)$. -/
def IsNontrivial (q a : ℕ) : Prop :=
  1 ≤ q ∧ 1 ≤ a ∧ Nat.Coprime q a ∧ (q, a) ≠ (1, 1)

/-- $Q(N) = \max Q(N; q, a)$, the largest number of perfect squares occurring among the first
$N$ terms of any non-trivial arithmetic progression. The supremum is over a set of naturals that
is bounded above by $N$ (each progression has only $N$ terms), so it is attained. -/
noncomputable def Qmax (N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ q a : ℕ, IsNontrivial q a ∧ Q N q a = m}

/-- Sanity check: the progression $24 n + 1$ is non-trivial. -/
@[category test, AMS 11]
theorem isNontrivial_24_1 : IsNontrivial 24 1 := by
  refine ⟨by norm_num, by norm_num, by decide, by decide⟩

/-- Sanity check: there are no squares among the first `0` terms of any progression. -/
@[category test, AMS 11]
theorem Q_zero (q a : ℕ) : Q 0 q a = 0 := by
  simp [Q]

/-- Sanity check pinning `Q` to a concrete value: among the first `6` terms of `24 n + 1`, namely
`1, 25, 49, 73, 97, 121`, exactly four are perfect squares (`1, 25, 49, 121`), so
`Q 6 24 1 = 4`. This validates the definition of `Q` and matches the claim that `24 n + 1` is the
extremal progression. -/
@[category test, AMS 11]
theorem Q_six_twentyfour_one : Q 6 24 1 = 4 := by
  show ({n : ℕ | n < 6 ∧ IsSquare (24 * n + 1)}).ncard = 4
  have hset : {n : ℕ | n < 6 ∧ IsSquare (24 * n + 1)} = ({0, 1, 2, 5} : Set ℕ) := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hn, hsq⟩
      interval_cases n
      · omega
      · omega
      · omega
      · exfalso; obtain ⟨r, hr⟩ := hsq
        have hb : r < 9 := by nlinarith
        interval_cases r <;> omega
      · exfalso; obtain ⟨r, hr⟩ := hsq
        have hb : r < 10 := by nlinarith
        interval_cases r <;> omega
      · omega
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨by norm_num, 1, by norm_num⟩
      · exact ⟨by norm_num, 5, by norm_num⟩
      · exact ⟨by norm_num, 7, by norm_num⟩
      · exact ⟨by norm_num, 11, by norm_num⟩
  rw [hset]
  have hcoe : ({0, 1, 2, 5} : Set ℕ) = ↑({0, 1, 2, 5} : Finset ℕ) := by simp
  rw [hcoe, Set.ncard_coe_finset]
  decide

/--
**Rudin's conjecture.** The maximal number of squares among the first $N$ terms of a non-trivial
arithmetic progression grows at most like $\sqrt{N}$:
$$Q(N) = O(\sqrt{N}).$$
-/
@[category research open, AMS 11]
theorem rudins_conjecture :
    (fun N : ℕ => (Qmax N : ℝ)) =O[atTop] fun N : ℕ => Real.sqrt N := by
  sorry

/--
A stronger form of Rudin's conjecture: for every $N \ge 6$, the arithmetic progression
$24 n + 1$ attains the maximum $Q(N)$.
-/
@[category research open, AMS 11]
theorem rudins_conjecture_strong (N : ℕ) (hN : 6 ≤ N) : Q N 24 1 = Qmax N := by
  sorry

/--
The strongest form of Rudin's conjecture also asserts *uniqueness*: for $N \ge 6$, any non-trivial
arithmetic progression attaining the maximum $Q(N)$ has common difference $24$. (Its initial term
is then forced by $\gcd(24, a) = 1$; the progression $24n + 1$ is the canonical representative.)
-/
@[category research open, AMS 11]
theorem rudins_conjecture_unique_neg :
    ¬ (∀ (N : ℕ) (hN : 6 ≤ N) (q a : ℕ)
    (hqa : IsNontrivial q a) (hmax : Q N q a = Qmax N), q = 24) := by
  classical
  intro H
  have hgap (x : ℕ) (hx : 49 ≤ x) :
      ¬ (IsSquare x ∧ IsSquare (x + 24)) := by
    rintro ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
    have hrs : r + 1 ≤ s := by
      by_contra h
      have hsr : s ≤ r := by omega
      have hmul := Nat.mul_le_mul hsr hsr
      omega
    have hstep := Nat.mul_le_mul hrs hrs
    have hrlo : 7 ≤ r := by
      by_contra h
      have hle : r ≤ 6 := by omega
      have hmul := Nat.mul_le_mul hle hle
      omega
    have hrhi : r ≤ 11 := by
      nlinarith only [hr, hs, hstep]
    have hrr : r * r ≤ 121 := Nat.mul_le_mul hrhi hrhi
    have hshi : s ≤ 12 := by
      by_contra h
      have hle : 13 ≤ s := by omega
      have hmul := Nat.mul_le_mul hle hle
      omega
    interval_cases r <;> interval_cases s <;> omega

  have h24 (a : ℕ) (ha : 1 ≤ a) : Q 6 24 a ≤ 4 := by
    let t : Finset ℕ :=
      {0, 1, if IsSquare (48 + a) then 2 else 3,
        if IsSquare (96 + a) then 4 else 5}
    have ht : t.card ≤ 4 := by
      dsimp only [t]
      split_ifs <;> norm_num
    have hsub :
        {n : ℕ | n < 6 ∧ IsSquare (24 * n + a)} ⊆
          (t : Set ℕ) := by
      intro n hn
      rcases hn with ⟨hn, hsq⟩
      interval_cases n
      · simp [t]
      · simp [t]
      · change IsSquare (48 + a) at hsq
        simp [t, hsq]
      · change IsSquare (72 + a) at hsq
        have hh : ¬ IsSquare (48 + a) := by
          intro hh
          apply hgap (48 + a) (by omega)
          refine ⟨hh, ?_⟩
          have he : (48 + a) + 24 = 72 + a := by omega
          rw [he]
          exact hsq
        simp [t, hh]
      · change IsSquare (96 + a) at hsq
        simp [t, hsq]
      · change IsSquare (120 + a) at hsq
        have hh : ¬ IsSquare (96 + a) := by
          intro hh
          apply hgap (96 + a) (by omega)
          refine ⟨hh, ?_⟩
          have he : (96 + a) + 24 = 120 + a := by omega
          rw [he]
          exact hsq
        simp [t, hh]
    calc
      Q 6 24 a ≤ (t : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub t.finite_toSet
      _ = t.card := Set.ncard_coe_finset t
      _ ≤ 4 := ht

  have hQle (q a : ℕ) : Q 6 q a ≤ 6 := by
    have hsub :
        {n : ℕ | n < 6 ∧ IsSquare (q * n + a)} ⊆
          Set.Iio 6 := fun _ hn => hn.1
    calc
      Q 6 q a ≤ (Set.Iio (6 : ℕ)).ncard :=
        Set.ncard_le_ncard hsub (Set.finite_Iio 6)
      _ = 6 := Set.ncard_Iio_nat 6

  let S : Set ℕ :=
    {m | ∃ q a : ℕ, IsNontrivial q a ∧ Q 6 q a = m}
  have hbd : BddAbove S := by
    refine ⟨6, ?_⟩
    rintro m ⟨q, a, hqa, rfl⟩
    exact hQle q a
  have hne : S.Nonempty :=
    ⟨Q 6 24 1, 24, 1, isNontrivial_24_1, rfl⟩
  have hm : Qmax 6 ∈ S := by
    change sSup S ∈ S
    exact Nat.sSup_mem hne hbd
  rcases hm with ⟨q, a, hqa, hmax⟩
  have hq : q = 24 := H 6 (by decide) q a hqa hmax
  have hu : Qmax 6 ≤ 4 := by
    calc
      Qmax 6 = Q 6 q a := hmax.symm
      _ = Q 6 24 a := by rw [hq]
      _ ≤ 4 := h24 a hqa.2.1

  have hc : IsNontrivial 120 49 :=
    ⟨by decide, by decide, by decide, by decide⟩
  have hlo : 4 ≤ Q 6 120 49 := by
    have hsub :
        (({0, 1, 2, 4} : Finset ℕ) : Set ℕ) ⊆
          {n : ℕ | n < 6 ∧ IsSquare (120 * n + 49)} := by
      intro n hn
      change n ∈ ({0, 1, 2, 4} : Finset ℕ) at hn
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl | rfl | rfl
      · exact ⟨by decide, 7, by decide⟩
      · exact ⟨by decide, 13, by decide⟩
      · exact ⟨by decide, 17, by decide⟩
      · exact ⟨by decide, 23, by decide⟩
    have hfin :
        {n : ℕ | n < 6 ∧ IsSquare (120 * n + 49)}.Finite :=
      (Set.finite_Iio (6 : ℕ)).subset (fun _ hn => hn.1)
    have hcount := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset] at hcount
    have hcard : ({0, 1, 2, 4} : Finset ℕ).card = 4 := by decide
    rw [hcard] at hcount
    exact hcount
  have hle : Q 6 120 49 ≤ Qmax 6 := by
    change Q 6 120 49 ≤ sSup S
    exact le_csSup hbd
      (show Q 6 120 49 ∈ S from ⟨120, 49, hc, rfl⟩)
  have heq : Q 6 120 49 = Qmax 6 := by omega
  have hbad : 120 = 24 := H 6 (by decide) 120 49 hc heq
  norm_num at hbad
