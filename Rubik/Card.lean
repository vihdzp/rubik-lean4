import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import Rubik.PRubik

/-!
We provide results on the cardinalities of our types. In particular, we count the number of
pre-Rubik's and Rubik's cubes.
-/

open Equiv

@[simp]
protected theorem EdgePiece.card : Fintype.card EdgePiece = 24 :=
  rfl

@[simp]
protected theorem Edge.card : Fintype.card Edge = 12 :=
  rfl

@[simp]
protected theorem Edge.perm_card : Fintype.card (Perm Edge) = 479001600 := by
  rw [Fintype.card_perm, Edge.card]
  rfl

@[simp]
protected theorem CornerPiece.card : Fintype.card CornerPiece = 24 :=
  rfl

@[simp]
protected theorem Corner.card : Fintype.card Corner = 8 :=
  rfl

@[simp]
protected theorem Corner.perm_card : Fintype.card (Perm Corner) = 40320 := by
  rw [Fintype.card_perm, Corner.card]
  rfl

namespace PRubik

/-- The combination of `PRubik.edgeEquiv` and `PRubik.cornerEquiv`. -/
def edgeCornerEquiv : PRubik →* Perm Edge × Perm Corner :=
  PRubik.edgeEquiv.prod PRubik.cornerEquiv

/- It's perfectly possible to provide a constructive proof, but it's a bit easier to do this via
choice. -/
theorem edgeCornerEquiv_surjective : Function.Surjective edgeCornerEquiv := by
  rintro ⟨f, g⟩
  let f' : EdgePiece → EdgePiece := fun e ↦ let x := (f ⟦e⟧).out
    if e = ⟦e⟧.out then x else x.flip
  let g' : CornerPiece → CornerPiece := fun c ↦ let x := (g ⟦c⟧).out
    if c = ⟦c⟧.out then x else if c = ⟦c⟧.out.cyclic then x.cyclic else x.cyclic.cyclic
  refine ⟨⟨Equiv.Perm.ofSurjective (f := f') ?_, Equiv.Perm.ofSurjective (f := g') ?_, ?_, ?_⟩, ?_⟩
  · intro e
    obtain he | he := EdgePiece.equiv_iff.1 (Quotient.mk_out e).symm
    · use (f.symm ⟦e⟧).out
      simpa [f'] using he.symm
    · use (f.symm ⟦e⟧).out.flip
      simpa [f'] using he.symm
  · intro c
    obtain hc | hc | hc := CornerPiece.equiv_iff'.1 (Quotient.mk_out c).symm
    · use (g.symm ⟦c⟧).out
      simpa [g'] using hc.symm
    · use (g.symm ⟦c⟧).out.cyclic
      simpa [g'] using hc.symm
    · use (g.symm ⟦c⟧).out.cyclic.cyclic
      simpa [g'] using hc.symm
  · intro e
    simp_rw [Perm.ofSurjective_apply, f']
    obtain he | he := EdgePiece.equiv_iff.1 (Quotient.mk_out e)
    · simp [he]
    · simp [he, e.flip_ne.symm]
  · intro c
    simp_rw [Perm.ofSurjective_apply, g', Corner.mk_cyclic, CornerPiece.cyclic_inj]
    obtain hc | hc | hc := CornerPiece.equiv_iff'.1 (Quotient.mk_out c)
    · simp [hc]
    · simp [hc, c.cyclic_ne.symm, c.cyclic_cyclic_ne.symm]
    · simp [hc, c.cyclic_ne.symm, c.cyclic_cyclic_ne.symm]
  · rw [edgeCornerEquiv, MonoidHom.prod_apply, Prod.mk.injEq]
    constructor
    · ext e
      refine e.inductionOn ?_
      intro e
      simp_rw [edgeEquiv_mk, f', Perm.ofSurjective_apply]
      split_ifs <;> simp
    · ext c
      refine c.inductionOn ?_
      intro c
      simp_rw [cornerEquiv_mk, g', Perm.ofSurjective_apply]
      split_ifs <;> simp

/-- The kernel of `edgeCornerEquiv` consists of cubes with only their edges flipped and corners
rotated. -/
def kerEdgeCornerEquiv : edgeCornerEquiv.ker ≃* (Edge → ℤˣ) × (Corner → Multiplicative (ZMod 3)) :=
  sorry

/-- There are 2¹² × 3⁸ × 8! × 12! pre-Rubik's cubes. -/
@[simp]
protected theorem card : Fintype.card PRubik = 519024039293878272000 := by
  simp_rw [← Nat.card_eq_fintype_card,
    Subgroup.card_eq_card_quotient_mul_card_subgroup PRubik.edgeCornerEquiv.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, MonoidHom.mem_range,
    ← Set.mem_range, edgeCornerEquiv_surjective.range_eq, Nat.card_univ,
    Nat.card_congr kerEdgeCornerEquiv.toEquiv, Nat.card_prod]
  simp

end PRubik

namespace Rubik

/-- There are 2¹² × 3⁸ × 8! × 11! Rubik's cubes. -/
@[simp]
protected theorem card : Fintype.card Rubik = 43252003274489856000 := by
  have := Subgroup.card_eq_card_quotient_mul_card_subgroup PRubik.invariant.ker
  simp_rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, MonoidHom.mem_range,
    ← Set.mem_range, PRubik.invariant_surjective.range_eq, Nat.card_univ] at this
  rw [← Nat.card_eq_fintype_card]
  apply (Nat.div_eq_of_eq_mul_right _ this).symm.trans
  · simp_rw [Nat.card_prod, Nat.card_eq_fintype_card, PRubik.card]
    simp
  · simp

end Rubik
