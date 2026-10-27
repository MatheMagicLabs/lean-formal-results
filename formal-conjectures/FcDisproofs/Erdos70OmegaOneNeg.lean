/-
Disproof of `omega_one` from google-deepmind/formal-conjectures (commit 84cf7f8),
file FormalConjectures/ErdosProblems/70.lean, where the statement is listed as open.

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
# Erdős Problem 70

*References:*
- [erdosproblems.com/70](https://www.erdosproblems.com/70)
- [ErRa56] Erdős, P. and Rado, R., *A partition calculus in set theory*,
  Bull. Amer. Math. Soc. **62** (1956), 427–489, Theorem 31.
- [Er87] Erdős, P., *Some problems on finite and infinite graphs*,
  Logic and combinatorics (Arcata, Calif., 1985), Contemp. Math. **65** (1987), 223–228.

The 3-uniform (triple) partition relation $\mathfrak{c} \to (\beta, n)^3_2$, where
$\mathfrak{c}$ denotes the order type of the real numbers with their usual order (written
$\lambda$ in [ErRa56]). This is the triple analogue of `OrdinalCardinalRamsey` used in
Problems 590–592; the file also contains the analogous relation for an ordinal in place
of the real line.
-/

@[expose] public section

open Cardinal Ordinal
open scoped Cardinal

namespace Erdos70

universe u

/- ### The 3-uniform partition relation -/

/--
`OrdinalCardinalRamsey3 α β c` asserts the 3-uniform ordinal Ramsey property
$\alpha \to (\beta, c)^3_2$.

It states that for any 2-coloring of all 3-element subsets of (the ordinal type) $\alpha$,
one of the following must hold:
* There is a red-monochromatic subset of order type $\beta$: every 3-element sub-subset is
  colored red. (Formally: a set $s \subseteq \alpha$ with $\operatorname{typeLT} s = \beta$
  such that any three distinct elements of $s$ are colored red.)
* There is a blue-monochromatic subset of cardinality $c$: a set $s \subseteq \alpha$ with
  $\#s = c$ such that every three distinct elements of $s$ are colored blue.

The coloring is given as a predicate `isRed : α.ToType → α.ToType → α.ToType → Prop` on
ordered triples of distinct elements; to faithfully encode a coloring of *unordered*
3-element subsets we additionally require `isRed` to be invariant under permutation of
its three (distinct) arguments.
-/
def OrdinalCardinalRamsey3 (α β : Ordinal.{u}) (c : Cardinal.{u}) : Prop :=
  -- For any partition of 3-element subsets into red and blue:
  ∀ (isRed : α.ToType → α.ToType → α.ToType → Prop),
    -- The colouring is well-defined on *unordered* triples of distinct elements:
    (∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (isRed x y z ↔ isRed y x z) ∧ (isRed x y z ↔ isRed x z y)) →
    -- either there is a red-monochromatic subset of order type β
    (∃ s : Set α.ToType, typeLT s = β ∧ s.Triplewise isRed) ∨
    -- or there is a blue-monochromatic subset of cardinality c
    (∃ s : Set α.ToType, #s = c ∧ s.Triplewise (fun x y z ↦ ¬ isRed x y z))

/--
`RealCardinalRamsey3 β c` asserts the 3-uniform partition relation
$\mathfrak{c} \to (\beta, c)^3_2$, where $\mathfrak{c}$ is the order type of the real
numbers with their usual order.

It states that for any 2-coloring of all 3-element subsets of $\mathbb{R}$,
one of the following must hold:
* There is a red-monochromatic subset of order type $\beta$: the range of an order embedding
  `β.ToType ↪o ℝ` such that any three distinct elements of the range are colored red.
* There is a blue-monochromatic subset of cardinality $c$: a set $s \subseteq \mathbb{R}$ with
  $\#s = c$ such that every three distinct elements of $s$ are colored blue.

The coloring is encoded as in `OrdinalCardinalRamsey3`: a predicate on ordered triples of
distinct reals that is invariant under permutation of its three arguments.
-/
def RealCardinalRamsey3 (β : Ordinal.{0}) (c : Cardinal.{0}) : Prop :=
  -- For any partition of 3-element subsets of `ℝ` into red and blue:
  ∀ (isRed : ℝ → ℝ → ℝ → Prop),
    -- The colouring is well-defined on *unordered* triples of distinct elements:
    (∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (isRed x y z ↔ isRed y x z) ∧ (isRed x y z ↔ isRed x z y)) →
    -- either there is a red-monochromatic subset of order type β
    (∃ e : β.ToType ↪o ℝ, (Set.range e).Triplewise isRed) ∨
    -- or there is a blue-monochromatic subset of cardinality c
    (∃ s : Set ℝ, #s = c ∧ s.Triplewise (fun x y z ↦ ¬ isRed x y z))

/- ### The main open problem -/

/--
**Erdős Problem 70**: Let $\mathfrak{c}$ be the order type of the real numbers,
let $\beta$ be a countable ordinal, and let $2 \le n < \omega$.
Is it true that $\mathfrak{c} \to (\beta, n)^3_2$?

Note: The cases $n \le 3$ are trivially true (compare `omega_three`), so the
genuine content of the conjecture begins at $n = 4$.
-/
@[category research open, question, AMS 3]
theorem erdos_70 :
    ∀ᵉ (β : Ordinal.{0}) (n : ℕ) (_ : β.card ≤ ℵ₀) (_ : 2 ≤ n),
      RealCardinalRamsey3 β n := by
  sorry

/- ### Variants -/

namespace erdos_70.variants

/--
**Erdős–Rado partial result**: $\mathfrak{c} \to (\omega + n, 4)^3_2$ for any
$2 \le n < \omega$, where $\mathfrak{c}$ is the order type of the real numbers.
Positive partial answer to Problem 70 with $\beta = \omega + n$ and the blue side
fixed at $4$ [ErRa56, Theorem 31].
-/
@[category research solved, AMS 3]
theorem erdos_rado (n : ℕ) (hn : 2 ≤ n) :
    RealCardinalRamsey3 (ω + n) 4 := by
  sorry

/--
**First open case beyond Erdős–Rado**: $\mathfrak{c} \to (\omega \cdot 2, 4)^3_2$,
where $\mathfrak{c}$ is the order type of the real numbers.

Erdős and Rado proved $\mathfrak{c} \to (\omega + n, 4)^3_2$ for every finite $n \ge 2$
(see `erdos_rado`), which covers all red ordinals below $\omega \cdot 2 = \omega + \omega$.
This variant asks whether the result extends to $\beta = \omega \cdot 2$, the simplest
countable ordinal not covered by their theorem.
-/
@[category research open, question, AMS 3]
theorem omega_times_two_four :
    RealCardinalRamsey3 (ω * 2) 4 := by
  sorry

/--
**Trivial boundary case**: $\mathfrak{c} \to (\omega, 3)^3_2$, stated for the initial
ordinal $\mathfrak{c}.\mathrm{ord}$ of the cardinality of the continuum.

This is trivially true because in a 3-uniform hypergraph, a \"blue clique of size 3\"
consists of a single 3-element subset ($\binom{3}{3} = 1$), so the blue alternative
merely asks for one blue triple to exist. The proof splits into two cases:
- If any blue triple exists, it is itself a blue-monochromatic set of cardinality 3.
- If no blue triple exists, all triples are red, and since $\omega \le \mathfrak{c}$,
  any subset of order type $\omega$ is red-monochromatic.

The problem becomes non-trivial only for $n \ge 4$; see `omega_times_two_four` for
the simplest genuinely open case.
-/
@[category research solved, question, AMS 3, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/c024db0fa3ac32c6dddcd6c28d7b0cd994dad580/FormalConjectures/ErdosProblems/70.lean#L126"]
theorem omega_three :
    OrdinalCardinalRamsey3 (𝔠).ord ω 3 := by
  sorry

/--
**The relation at $\omega_1$**: $\mathfrak{c} \to (\omega_1, n)^3_2$ for finite $n \ge 2$,
where $\omega_1 = \aleph_1$ is the first uncountable ordinal.

Note that $\omega_1$ is *not* a countable ordinal, so this is not directly an instance of the
main Erdős problem (which asks for *countable* $\beta$). Under CH, $\omega_1 = \mathfrak{c}.\mathrm{ord}$,
making this a self-referential question about $\mathfrak{c}.\mathrm{ord} \to
(\mathfrak{c}.\mathrm{ord}, n)^3_2$.
-/
@[category research open, question, AMS 3]
theorem omega_one_neg :
    ¬ (∀ᵉ (n : ℕ) (_ : 2 ≤ n),
      OrdinalCardinalRamsey3 (𝔠).ord (Cardinal.aleph 1).ord n) := by
  classical
  intro h
  have h4 := h 4 (by norm_num)
  let A : Type _ := (𝔠).ord.ToType
  change ∀ R : A → A → A → Prop,
      (∀ x y z, x ≠ y → y ≠ z → x ≠ z →
        (R x y z ↔ R y x z) ∧ (R x y z ↔ R x z y)) →
      (∃ s : Set A, typeLT s = (Cardinal.aleph 1).ord ∧
        s.Triplewise R) ∨
      (∃ s : Set A, #s = 4 ∧
        s.Triplewise (fun x y z => ¬ R x y z)) at h4
  obtain ⟨f⟩ : Nonempty (A ≃ ℝ) :=
    Cardinal.lift_mk_eq'.mp (by simp [A, Cardinal.mk_real])

  have hcount (t : Set A)
      (hm : StrictMono (fun x : t => f x) ∨
        StrictAnti (fun x : t => f x)) : t.Countable := by
    letI : SuccOrder t := SuccOrder.ofLinearWellFoundedLT t
    change Countable t
    apply Set.countable_univ_iff.mp
    rcases hm with hm | hm
    · refine ((countable_image_lt_image_Ioi (fun x : t => f x)).union
        (Set.countable_isTop t)).mono ?_
      intro x _
      by_cases hx : IsMax x
      · exact Or.inr hx.isTop
      · exact Or.inl
          ⟨f ((Order.succ x : t) : A),
            hm (Order.lt_succ_of_not_isMax hx),
            fun y hxy => hm.monotone (Order.succ_le_of_lt hxy)⟩
    · refine ((countable_image_gt_image_Ioi (fun x : t => f x)).union
        (Set.countable_isTop t)).mono ?_
      intro x _
      by_cases hx : IsMax x
      · exact Or.inr hx.isTop
      · exact Or.inl
          ⟨f ((Order.succ x : t) : A),
            hm (Order.lt_succ_of_not_isMax hx),
            fun y hxy => hm.antitone (Order.succ_le_of_lt hxy)⟩

  let peak : A → A → A → Prop := fun x y z =>
    x < y ∧ y < z ∧ f x < f y ∧ f z < f y
  let R : A → A → A → Prop := fun x y z =>
    ¬ (peak x y z ∨ peak x z y ∨ peak y x z ∨
      peak y z x ∨ peak z x y ∨ peak z y x)

  have hswap (x y z : A) : R x y z → R y x z := by
    intro hr hp
    apply hr
    rcases hp with hp | hp | hp | hp | hp | hp
    · exact Or.inr (Or.inr (Or.inl hp))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hp)))
    · exact Or.inl hp
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hp))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))

  have hlast (x y z : A) : R x y z → R x z y := by
    intro hr hp
    apply hr
    rcases hp with hp | hp | hp | hp | hp | hp
    · exact Or.inr (Or.inl hp)
    · exact Or.inl hp
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hp))))
    · exact Or.inr (Or.inr (Or.inl hp))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hp)))

  have hsym : ∀ x y z : A, x ≠ y → y ≠ z → x ≠ z →
      (R x y z ↔ R y x z) ∧ (R x y z ↔ R x z y) := by
    intro x y z _ _ _
    exact ⟨⟨hswap x y z, hswap y x z⟩,
      ⟨hlast x y z, hlast x z y⟩⟩

  have hsort (x y z : A) (hxy : x < y) (hyz : y < z) :
      R x y z ↔ ¬ (f x < f y ∧ f z < f y) := by
    simp only [R, peak, hxy, hyz, hxy.trans hyz,
      not_lt_of_ge hxy.le, not_lt_of_ge hyz.le,
      not_lt_of_ge (hxy.trans hyz).le,
      true_and, false_and, or_false, false_or]

  rcases h4 R hsym with ⟨s, htype, hs⟩ | ⟨s, hcard, hs⟩
  · have hred {a b c : A}
        (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
        (hab : a < b) (hbc : b < c) :
        ¬ (f a < f b ∧ f c < f b) :=
      (hsort a b c hab hbc).mp
        (hs ha hb hc hab.ne hbc.ne (hab.trans hbc).ne)

    let t : Set A :=
      {x | x ∈ s ∧ ∀ y ∈ s, y < x → f x < f y}
    have ht : t.Countable := hcount t (Or.inr (by
      intro x y hxy
      exact y.property.2 x.val x.property.1 hxy))

    have hu : (s \ t).Countable := hcount (s \ t) (Or.inl (by
      intro x y hxy
      have hxy' : (x : A) < (y : A) := hxy
      have hx : ¬ ∀ a ∈ s, a < (x : A) → f x < f a := by
        intro hx
        exact x.property.2 ⟨x.property.1, hx⟩
      push_neg at hx
      obtain ⟨a, ha, hax, hfa⟩ := hx
      have hfa' : f a < f x :=
        lt_of_le_of_ne hfa (fun he => hax.ne (f.injective he))
      apply lt_of_not_ge
      intro hyx
      have hfy : f y < f x :=
        lt_of_le_of_ne hyx (fun he => hxy'.ne' (f.injective he))
      exact hred ha x.property.1 y.property.1 hax hxy'
        ⟨hfa', hfy⟩))

    have hsc : s.Countable := (ht.union hu).mono (by
      intro x hx
      by_cases hxt : x ∈ t
      · exact Or.inl hxt
      · exact Or.inr ⟨hx, hxt⟩)

    have hcard : #s = Cardinal.aleph 1 := by
      simpa only [Ordinal.card_type, Cardinal.card_ord] using
        congrArg Ordinal.card htype
    have hle := hsc.le_aleph0
    rw [hcard] at hle
    exact (not_le_of_gt Cardinal.aleph0_lt_aleph_one) hle

  · have hblue {a b c : A}
        (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
        (hab : a < b) (hbc : b < c) :
        f a < f b ∧ f c < f b := by
      by_contra hn
      exact hs ha hb hc hab.ne hbc.ne (hab.trans hbc).ne
        ((hsort a b c hab hbc).mpr hn)

    obtain ⟨t, ht, hn⟩ :=
      Cardinal.mk_set_eq_nat_iff_finset.mp hcard
    let e : Fin 4 ↪o A := t.orderEmbOfFin hn
    have he (i : Fin 4) : e i ∈ s := by
      rw [← ht]
      exact t.orderEmbOfFin_mem hn i
    have h01 : e 0 < e 1 := e.strictMono (by decide)
    have h12 : e 1 < e 2 := e.strictMono (by decide)
    have h23 : e 2 < e 3 := e.strictMono (by decide)
    have h012 := hblue (he 0) (he 1) (he 2) h01 h12
    have h123 := hblue (he 1) (he 2) (he 3) h12 h23
    exact (not_lt_of_ge h012.2.le) h123.1
