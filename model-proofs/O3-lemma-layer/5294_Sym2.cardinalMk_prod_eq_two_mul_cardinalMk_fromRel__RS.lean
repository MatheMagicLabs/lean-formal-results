/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_eq_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 130
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
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

theorem cardinalMk_prod_eq_two_mul_cardinalMk_fromRel [Std.Irrefl r] :
    #{ p : α × α // r p.fst p.snd } = 2 * #(fromRel sym) := by
  classical
  let f : {p : α × α // r p.fst p.snd} → fromRel sym :=
    fun p => ⟨s(p.1.1, p.1.2), fromRel_prop.mpr p.2⟩
  rw [← Cardinal.mk_congr (Equiv.sigmaFiberEquiv f), Cardinal.mk_sigma]
  have h : ∀ z : fromRel sym, #{x // f x = z} = 2 := by
    rintro ⟨z, hz⟩
    induction z using Sym2.ind with
    | h a b =>
      have hab : r a b := fromRel_prop.mp hz
      have hne : a ≠ b := by
        rintro rfl
        exact Std.Irrefl.irrefl a hab
      rw [Cardinal.mk_eq_two_iff]
      refine ⟨⟨⟨(a, b), hab⟩, Subtype.ext rfl⟩,
        ⟨⟨(b, a), sym.symm _ _ hab⟩,
          Subtype.ext (by show s(b, a) = s(a, b); exact Sym2.eq_swap)⟩, ?_, ?_⟩
      · intro h
        have := congrArg (fun q => q.1.1.1) h
        exact hne this
      · ext ⟨⟨⟨c, d⟩, hcd⟩, hf⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        have h2 : s(c, d) = s(a, b) := congrArg Subtype.val hf
        rcases Sym2.eq_iff.mp h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · left; rfl
        · right; rfl
  rw [show (fun z => #{x // f x = z}) = fun _ => 2 from funext h]
  rw [Cardinal.sum_const', mul_comm]
