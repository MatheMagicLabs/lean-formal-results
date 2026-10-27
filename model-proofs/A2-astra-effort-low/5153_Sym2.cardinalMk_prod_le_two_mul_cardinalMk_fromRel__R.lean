/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_le_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Sym2
open scoped Cardinal
variable {α : Type*}
variable (α) in
open scoped Classical in
variable (α) in
variable (α) in
variable (α) in
open scoped Classical in
variable (α) in
variable (α) in
section fromRel
variable {r : α → α → Prop} (sym : Std.Symm r)

theorem cardinalMk_prod_le_two_mul_cardinalMk_fromRel :
    #{ p : α × α // r p.fst p.snd } ≤ 2 * #(fromRel sym) := by
  classical
  have key (x y z : α × α)
      (hx : s(x.1, x.2) = s(z.1, z.2))
      (hy : s(y.1, y.2) = s(z.1, z.2))
      (hb : decide (x.1 = z.1) = decide (y.1 = z.1)) :
      x = y := by
    rcases x with ⟨a, b⟩
    rcases y with ⟨c, d⟩
    rcases z with ⟨u, v⟩
    simp only [Sym2.eq_iff] at hx hy
    by_cases h₁ : a = u <;>
      by_cases h₂ : c = u <;>
      simp_all [Prod.ext_iff] <;> aesop
  let P := {p : α × α // r p.fst p.snd}
  let f : P → fromRel sym := fun p =>
    ⟨s(p.val.fst, p.val.snd), by simpa using p.property⟩
  let rep : P → P := fun p =>
    Classical.choose (show ∃ q, f q = f p from ⟨p, rfl⟩)
  have hrep (p : P) : f (rep p) = f p :=
    Classical.choose_spec (show ∃ q, f q = f p from ⟨p, rfl⟩)
  let g : P → Bool × fromRel sym := fun p =>
    (decide (p.val.fst = (rep p).val.fst), f p)
  have hg : Function.Injective g := by
    intro p q hpq
    have hf : f p = f q := congrArg Prod.snd hpq
    have hr : rep p = rep q := by
      dsimp [rep]
      simp only [hf]
    have hb := congrArg Prod.fst hpq
    change decide (p.val.fst = (rep p).val.fst) =
      decide (q.val.fst = (rep q).val.fst) at hb
    rw [← hr] at hb
    have hp := congrArg Subtype.val (hrep p)
    have hq := congrArg Subtype.val (hrep q)
    rw [← hr] at hq
    apply Subtype.ext
    exact key p.val q.val (rep p).val hp.symm hq.symm hb
  simpa [Cardinal.mk_prod] using Cardinal.mk_le_of_injective hg
