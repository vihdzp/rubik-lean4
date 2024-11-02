import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import Rubik.Algorithm

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

@[simp]
theorem edgeCornerEquiv_apply (cube : PRubik) :
    edgeCornerEquiv cube = (edgeEquiv cube, cornerEquiv cube) :=
  rfl

theorem mem_ker_edgeCornerEquiv {cube : PRubik} :
    cube ∈ edgeCornerEquiv.ker ↔ edgeEquiv cube = 1 ∧ cornerEquiv cube = 1 := by
  rw [MonoidHom.mem_ker, edgeCornerEquiv_apply, Prod.mk_eq_one]

theorem edgeEquiv_of_mem_ker_edgeCornerEquiv (h : cube ∈ edgeCornerEquiv.ker) :
    edgeEquiv cube = 1 :=
  (mem_ker_edgeCornerEquiv.1 h).1

theorem cornerEquiv_of_mem_ker_edgeCornerEquiv (h : cube ∈ edgeCornerEquiv.ker) :
    cornerEquiv cube = 1 :=
  (mem_ker_edgeCornerEquiv.1 h).2

/-- A computable inverse for `edgeCornerEquiv`. -/
def edgeCornerEquiv_inv (p : Perm Edge × Perm Corner) : PRubik := by
  let f' : EdgePiece → EdgePiece := fun e ↦ let x := (p.1 ⟦e⟧).out
    if e = Edge.out ⟦e⟧ then x else x.flip
  let g' : CornerPiece → CornerPiece := fun c ↦ let x := (p.2 ⟦c⟧).out
    if c = Corner.out ⟦c⟧ then x else
      if c = (Corner.out ⟦c⟧).cyclic then x.cyclic else x.cyclic.cyclic
  refine ⟨Equiv.Perm.ofSurjective f' ?_, Equiv.Perm.ofSurjective g' ?_, ?_, ?_⟩
  · intro e
    obtain he | he := EdgePiece.equiv_iff.1 (Edge.mk_out e).symm
    · use (p.1.symm ⟦e⟧).out
      simpa [f'] using he.symm
    · use (p.1.symm ⟦e⟧).out.flip
      simpa [f'] using he.symm
  · intro c
    obtain hc | hc | hc := CornerPiece.equiv_iff'.1 (Corner.mk_out c).symm
    · use (p.2.symm ⟦c⟧).out
      simpa [g'] using hc.symm
    · use (p.2.symm ⟦c⟧).out.cyclic
      simpa [g'] using hc.symm
    · use (p.2.symm ⟦c⟧).out.cyclic.cyclic
      simpa [g'] using hc.symm
  · intro e
    simp_rw [Perm.ofSurjective_apply, f']
    obtain he | he := EdgePiece.equiv_iff.1 (Edge.mk_out e) <;>
    simp [he, e.flip_ne.symm]
  · intro c
    simp_rw [Perm.ofSurjective_apply, g', Corner.mk_cyclic, CornerPiece.cyclic_inj]
    obtain hc | hc | hc := CornerPiece.equiv_iff'.1 (Corner.mk_out c) <;>
    simp [hc, c.cyclic_ne.symm, c.cyclic_cyclic_ne.symm]

theorem edgeCornerEquiv_leftInverse : Function.LeftInverse edgeCornerEquiv edgeCornerEquiv_inv := by
  intro x
  rw [edgeCornerEquiv_apply, Prod.mk.injEq]
  constructor <;> ext x <;> refine x.inductionOn ?_ <;> intro x
  · simp_rw [edgeEquiv_mk, edgeCornerEquiv_inv, Perm.ofSurjective_apply]
    split_ifs <;> simp
  · simp_rw [cornerEquiv_mk, edgeCornerEquiv_inv, Perm.ofSurjective_apply]
    split_ifs <;> simp

theorem edgeCornerEquiv_surjective : Function.Surjective edgeCornerEquiv :=
  edgeCornerEquiv_leftInverse.surjective

/-- The kernel of `edgeCornerEquiv` consists of cubes with only their edges flipped and corners
rotated. -/
def kerEdgeCornerEquiv :
    edgeCornerEquiv.ker ≃* (Edge → ℤˣ) × (Corner → Multiplicative (ZMod 3)) := by
  refine ⟨⟨fun cube ↦ (cube.1.edgeValue, Multiplicative.ofAdd ∘ cube.1.cornerValue),
    fun x ↦
      let f : EdgePiece → EdgePiece := fun e ↦ if x.1 ⟦e⟧ = 1 then e else e.flip
      let g : CornerPiece → CornerPiece := fun c ↦ if x.2 ⟦c⟧ = 1 then c else
        if x.2 ⟦c⟧ = Multiplicative.ofAdd 1 then c.cyclic else c.cyclic.cyclic
      let g' : CornerPiece → CornerPiece := fun c ↦ if x.2 ⟦c⟧ = 1 then c else
        if x.2 ⟦c⟧ = Multiplicative.ofAdd 1 then c.cyclic.cyclic else c.cyclic
      have hf (e) : f (f e) = e := by
        simp_rw [f]
        split_ifs with h₁ h₂
        · rfl
        · rw [Edge.mk_flip] at h₂
          contradiction
        · exact e.flip₂
    ⟨⟨⟨f, f, hf, hf⟩, ⟨g, g', ?_, ?_⟩, ?_, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩
  · intro c
    simp_rw [g, g']
    split_ifs <;> (simp at *; try contradiction)
  · intro c
    simp_rw [g, g']
    split_ifs <;> (simp at *; try contradiction)
  · intro e
    simp_rw [f, coe_fn_mk, Edge.mk_flip]
    split_ifs <;> simp
  · intro c
    simp_rw [g, coe_fn_mk, Corner.mk_cyclic]
    split_ifs <;> simp
  · rw [MonoidHom.mem_ker, edgeCornerEquiv_apply, Prod.mk.injEq]
    constructor
    · ext e
      refine e.inductionOn ?_
      intro e
      simp_rw [f, edgeEquiv_mk, coe_fn_mk]
      split_ifs <;> simp
    · ext c
      refine c.inductionOn ?_
      intro c
      simp_rw [g, g', cornerEquiv_mk, coe_fn_mk]
      split_ifs <;> simp
  · intro cube
    ext x
    · rw [coe_fn_mk]
      split_ifs with h
      · rw [eq_comm]
        simpa [edgeValue_mk] using h
      · simp_rw [edgeValue_mk, ite_eq_left_iff, neg_units_ne_self, imp_false, Decidable.not_not,
          ← edgeValue_eq_one] at h
        rwa [eq_comm, ← edgeValue_eq_neg_one (edgeEquiv_of_mem_ker_edgeCornerEquiv cube.2),
          ← Int.units_ne_iff_eq_neg]
    · have hc := cornerEquiv_of_mem_ker_edgeCornerEquiv cube.2
      rw [coe_fn_mk, eq_comm]
      split_ifs with h₁ h₂
      · simp_rw [Function.comp_apply, ofAdd_eq_one] at h₁
        rwa [cornerValue_eq_zero hc] at h₁
      · simp_rw [Function.comp_apply, EmbeddingLike.apply_eq_iff_eq] at h₂
        rwa [cornerValue_eq_one hc] at h₂
      · simp_rw [Function.comp_apply, ofAdd_eq_one] at h₁
        simp_rw [Function.comp_apply, EmbeddingLike.apply_eq_iff_eq] at h₂
        rw [← cornerValue_eq_two hc]
        exact ((ZMod.cases _).resolve_left h₁).resolve_left h₂
  · intro x
    ext y
    · refine y.inductionOn ?_
      intro e
      simp_rw [edgeValue_mk, coe_fn_mk, ite_eq_left_iff, EdgePiece.flip_ne, imp_false, not_not]
      split_ifs with h
      · rw [h]
      · rw [← ne_eq, Int.units_ne_iff_eq_neg] at h
        rw [h]
    · refine y.inductionOn ?_
      intro c
      simp_rw [Function.comp_apply, cornerValue_mk, coe_fn_mk]
      split_ifs with h₁ h₂
      · simp [h₁]
      · simp [h₂]
      · rw [eq_comm]
        simpa [mul_assoc] using ((ZMod.cases _).resolve_left h₁).resolve_left h₂
  · intro cube₁ cube₂
    simp_rw [Subgroup.coe_mul, Prod.mk_mul_mk, Prod.mk.injEq]
    constructor
    · funext e
      exact edgeValue_mul (edgeEquiv_of_mem_ker_edgeCornerEquiv cube₁.2)
        (edgeEquiv_of_mem_ker_edgeCornerEquiv cube₂.2) _
    · funext c
      exact cornerValue_mul (cornerEquiv_of_mem_ker_edgeCornerEquiv cube₁.2)
        (cornerEquiv_of_mem_ker_edgeCornerEquiv cube₂.2) _

/-- There are 2¹² × 3⁸ × 8! × 12! pre-Rubik's cubes. -/
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
protected theorem card : Fintype.card Rubik = 43252003274489856000 := by
  have := Subgroup.card_eq_card_quotient_mul_card_subgroup PRubik.invariant.ker
  simp_rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, MonoidHom.mem_range,
    ← Set.mem_range, PRubik.invariant_surjective.range_eq, Nat.card_univ] at this
  rw [← Nat.card_eq_fintype_card]
  apply (Nat.div_eq_of_eq_mul_right _ this).symm.trans
  · simp_rw [Nat.card_prod, Nat.card_eq_fintype_card, PRubik.card]
    simp
  · simp

/-- `Rubik.card` stated in terms of the `IsSolvable` predicate. -/
theorem card_solvable : Fintype.card { x : PRubik // x.IsSolvable } = 43252003274489856000 := by
  simp_rw [PRubik.isSolvable_iff_isValid]
  exact Rubik.card

end Rubik
