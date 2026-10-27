/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_eq_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 130
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
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
  let f : {p : α × α // r p.1 p.2} → fromRel sym :=
    fun p => ⟨s(p.1.1, p.1.2), fromRel_prop.2 p.2⟩
  have h2 : ∀ z, #{x // f x = z} = 2 := by
    rintro ⟨z, hz⟩
    obtain ⟨⟨a, b⟩, rfl⟩ := Sym2.mk_surjective z
    have hab : r a b := fromRel_prop.1 hz
    rw [Cardinal.mk_eq_two_iff]
    refine ⟨⟨⟨(a, b), hab⟩, rfl⟩,
      ⟨⟨(b, a), sym.symm a b hab⟩,
        Subtype.ext (show s(b, a) = s(a, b) from Sym2.eq_swap)⟩, ?_, ?_⟩
    · intro h
      have h1 : (a, b) = (b, a) := congrArg (fun x => x.1.1) h
      have hab' : a = b := (Prod.mk.inj h1).1
      subst hab'
      exact Std.Irrefl.irrefl _ hab
    · ext ⟨⟨⟨x, y⟩, hxy⟩, hf⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      have h' : s(x, y) = s(a, b) := congrArg Subtype.val hf
      rcases Sym2.eq_iff.1 h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left; rfl
      · right; rfl
  rw [← Cardinal.mk_congr (Equiv.sigmaFiberEquiv f), Cardinal.mk_sigma]
  simp_rw [h2]
  rw [Cardinal.sum_const', mul_comm]
