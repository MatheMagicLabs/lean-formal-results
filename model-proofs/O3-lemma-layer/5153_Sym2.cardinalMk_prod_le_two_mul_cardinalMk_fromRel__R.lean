/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_le_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  have hrep : ∀ z : Sym2 α, ∃ p : α × α, s(p.1, p.2) = z :=
    fun z => Sym2.ind (fun x y => ⟨(x, y), rfl⟩) z
  let rep : Sym2 α → α × α := fun z => Classical.choose (hrep z)
  have hrep' : ∀ z, s((rep z).1, (rep z).2) = z := fun z => Classical.choose_spec (hrep z)
  have key : ∀ z : fromRel sym, r (rep z.1).1 (rep z.1).2 := by
    intro z
    have h := z.2
    rw [← hrep' z.1] at h
    exact fromRel_prop.1 h
  let g : (fromRel sym) × Bool → { p : α × α // r p.fst p.snd } := fun x =>
    bif x.2 then ⟨rep x.1.1, key x.1⟩
    else ⟨(rep x.1.1).swap, sym.symm _ _ (key x.1)⟩
  have hg : Function.Surjective g := by
    rintro ⟨⟨a, b⟩, h⟩
    have hz : s(a, b) ∈ fromRel sym := fromRel_prop.2 h
    have e := hrep' s(a, b)
    rcases Sym2.eq_iff.1 e with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨(⟨s(a, b), hz⟩, true), ?_⟩
      apply Subtype.ext
      show rep s(a, b) = (a, b)
      exact Prod.ext h1 h2
    · refine ⟨(⟨s(a, b), hz⟩, false), ?_⟩
      apply Subtype.ext
      show (rep s(a, b)).swap = (a, b)
      exact Prod.ext h2 h1
  calc #{ p : α × α // r p.fst p.snd } ≤ #((fromRel sym) × Bool) :=
        Cardinal.mk_le_of_surjective hg
    _ = 2 * #(fromRel sym) := by
        rw [Cardinal.mk_prod, Cardinal.lift_uzero, Cardinal.mk_bool]
        first
          | (rw [Cardinal.lift_ofNat, mul_comm])
          | (simp [mul_comm])
