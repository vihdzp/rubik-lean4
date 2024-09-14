import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Units
import Rubik.Piece

/-!
Defines the type of "pre-Rubik's cubes". Thes are all possible Rubik's cubes that can be assembled
by using the 8 availble edges and 12 available corners. In particular, there is no regard for
solvability, and "impossible" positions like a flipped edge or rotated corner are allowed.

We define a group structure in `PRubik`, and define the "Rubik's cube invariant", a surjective group
homomorphism into `ℤ₂ × ℤ₂ × ℤ₃` whose kernel will be shown to consist of precisely the solvable
Rubik's cubes.
-/

open Orientation Equiv

/-- A pre-Rubik's cube. We represent this as a permutation of the edge pieces, and a permutation of
the corner pieces, such that pieces in the same edge or corner get mapped to the same edge or
corner.

This can be thought as the type of Rubik's cubes that can be physically assembled, without regard
for the solvability invariants. -/
structure PRubik : Type where
  /-- Returns the edge piece at a given location. -/
  edgePieceEquiv : Perm EdgePiece
  /-- Returns the corner piece at a given location. -/
  cornerPieceEquiv : Perm CornerPiece
  /-- Pieces in the same edge get mapped to pieces in the same edge. -/
  edge_flip (e : EdgePiece) : edgePieceEquiv e.flip = (edgePieceEquiv e).flip
  /-- Pieces in the same corner get mapped to pieces in the same corner. -/
  corner_cyclic (c : CornerPiece) : cornerPieceEquiv c.cyclic = (cornerPieceEquiv c).cyclic

attribute [simp] PRubik.edge_flip PRubik.corner_cyclic

namespace PRubik

deriving instance Fintype for PRubik

@[ext]
theorem ext (cube₁ cube₂ : PRubik)
    (he : ∀ e, cube₁.edgePieceEquiv e = cube₂.edgePieceEquiv e)
    (hc : ∀ c, cube₁.cornerPieceEquiv c = cube₂.cornerPieceEquiv c) :
    cube₁ = cube₂ := by
  obtain ⟨e₁, c₁, _, _⟩ := cube₁
  obtain ⟨e₂, c₂, _, _⟩ := cube₂
  simp
  rw [Equiv.ext_iff, Equiv.ext_iff]
  exact ⟨he, hc⟩

instance decEq : DecidableEq PRubik :=
  fun _ _ ↦ decidable_of_iff _ PRubik.ext_iff.symm

/-- An auxiliary function to get an edge piece in a cube, inferring the adjacency hypothesis. -/
def edgePiece (cube : PRubik) (a b : Orientation) (h : IsAdjacent a b := by decide) : EdgePiece :=
  cube.edgePieceEquiv ⟨a, b, h⟩

/-- An auxiliary function to get a corner piece in a cube, inferring the adjacency hypothesis. -/
def cornerPiece (cube : PRubik) (a b c : Orientation) (h : IsAdjacent₃ a b c := by decide) :
    CornerPiece :=
  cube.cornerPieceEquiv ⟨a, b, c, h⟩

/-- A list with all non-equivalent edges. This is an auxiliary function for the `PRubik.Repr`
instance. -/
private def edges : List EdgePiece :=
  [EdgePiece.mk' U B, EdgePiece.mk' U L, EdgePiece.mk' U R, EdgePiece.mk' U F,
    EdgePiece.mk' L B, EdgePiece.mk' L F, EdgePiece.mk' F R, EdgePiece.mk' R B,
    EdgePiece.mk' D B, EdgePiece.mk' D L, EdgePiece.mk' D R, EdgePiece.mk' D F]

/-- The corners in a Rubik's cube. This is an auxiliary function for the `Repr` instance. -/
private def corners (cube : PRubik) : List CornerPiece :=
  [cube.cornerPiece U B L, cube.cornerPiece U R B, cube.cornerPiece U L F, cube.cornerPiece U F R,
    cube.cornerPiece D L B, cube.cornerPiece D B R, cube.cornerPiece D F L, cube.cornerPiece D R F]

open Std.Format in
instance : Repr PRubik := ⟨fun cube _ ↦
  let e := edges.map cube.edgePieceEquiv
  let c := cube.corners
  have : e.length = 12 := rfl
  have : c.length = 8 := rfl
  let space := text "⬛⬛⬛"
  -- Up face
  space ++ c[0].fst ++ e[0].fst ++ c[1].fst ++ space ++ line
    ++ space ++ e[1].fst ++ U ++ e[2].fst ++ space ++ line
    ++ space ++ c[2].fst ++ e[3].fst ++ c[3].fst ++ space ++ line
  -- Left, front, and right faces
  ++ c[0].thd ++ e[1].snd ++ c[2].snd ++ c[2].thd ++ e[3].snd ++
    c[3].snd ++ c[3].thd ++ e[2].snd ++ c[1].snd ++ line
  ++ e[4].fst ++ L ++ e[5].fst ++ e[5].snd ++ F ++ e[6].fst ++ e[6].snd ++ R ++ e[7].fst ++ line
  ++ c[4].snd ++ e[9].snd ++ c[6].thd ++ c[6].snd ++ e[11].snd ++
    c[7].thd ++ c[7].snd ++ e[10].snd ++ c[5].thd ++ line
  -- Down face
  ++ space ++ c[6].fst ++ e[11].fst ++ c[7].fst ++ space ++ line
    ++ space ++ e[9].fst ++ D ++ e[10].fst ++ space ++ line
    ++ space ++ c[4].fst ++ e[8].fst ++ c[5].fst ++ space ++ line
  -- Back face
  ++ space ++ c[4].thd ++ e[8].snd ++ c[5].snd ++ space ++ line
    ++ space ++ e[4].snd ++ B ++ e[7].snd ++ space ++ line
    ++ space ++ c[0].snd ++ e[0].snd ++ c[1].thd ++ space⟩

/-- The solved Rubik's cube. -/
@[simps]
instance : One PRubik :=
  ⟨Equiv.refl _, Equiv.refl _, fun _ ↦ rfl, fun _ ↦ rfl⟩

instance : Inhabited PRubik := ⟨1⟩

/-- The solved Rubik's cube. -/
abbrev Solved : PRubik := 1

/-- The product of two Rubik's cubes is the Rubik's cube where the second's scramble is performed
after the first's.

Note that this is **opposite** to how function composition is usually defined. -/
@[simps]
instance : Mul PRubik :=
  ⟨fun cube₁ cube₂ ↦ by
    refine ⟨cube₂.edgePieceEquiv.trans cube₁.edgePieceEquiv,
      cube₂.cornerPieceEquiv.trans cube₁.cornerPieceEquiv, fun e ↦ ?_, fun c ↦ ?_⟩
    · dsimp
      rw [cube₂.edge_flip, cube₁.edge_flip]
    · dsimp
      rw [cube₂.corner_cyclic, cube₁.corner_cyclic]⟩

@[simp]
theorem edge_flip_symm (cube : PRubik) (e : EdgePiece) :
    cube.edgePieceEquiv.symm e.flip = (cube.edgePieceEquiv.symm e).flip := by
  conv_rhs => rw [← cube.edgePieceEquiv.symm_apply_apply (EdgePiece.flip _)]
  rw [cube.edge_flip, Equiv.apply_symm_apply]

@[simp]
theorem corner_cyclic_symm (cube : PRubik) (c : CornerPiece) :
    cube.cornerPieceEquiv.symm c.cyclic = (cube.cornerPieceEquiv.symm c).cyclic := by
  conv_rhs => rw [← cube.cornerPieceEquiv.symm_apply_apply (CornerPiece.cyclic _)]
  rw [cube.corner_cyclic, Equiv.apply_symm_apply]

theorem edgePieceEquiv_equiv (cube : PRubik) {e₁ e₂ : EdgePiece} (h : e₁ ≈ e₂) :
    cube.edgePieceEquiv e₁ ≈ cube.edgePieceEquiv e₂ := by
  obtain rfl | rfl := EdgePiece.equiv_iff.1 h
  · rfl
  · rw [edge_flip]
    exact EdgePiece.flip_equiv _

theorem cornerPieceEquiv_equiv (cube : PRubik) {c₁ c₂ : CornerPiece} (h : c₁ ≈ c₂) :
    cube.cornerPieceEquiv c₁ ≈ cube.cornerPieceEquiv c₂ := by
  obtain rfl | rfl | rfl := CornerPiece.equiv_iff.1 h
  · rfl
  · rw [corner_cyclic]
    exact CornerPiece.cyclic_equiv _
  · rw [corner_cyclic]
    exact (CornerPiece.cyclic_equiv _).symm

/-- The inverse of a Rubik's cube is obtained by performing its moves backwards. -/
@[simps]
instance : Inv PRubik :=
  ⟨fun cube ↦ ⟨cube.edgePieceEquiv.symm, cube.cornerPieceEquiv.symm,
    cube.edge_flip_symm, cube.corner_cyclic_symm⟩⟩

/-- The "pre-Rubik's cube" group. This isn't the true Rubik's cube group as it contains positions
that are unreachable by valid moves. -/
instance : Group PRubik where
  mul_assoc a b c := by ext <;> rfl
  one_mul a := by ext <;> rfl
  mul_one a := by ext <;> rfl
  inv_mul_cancel a := by ext <;> simp

/-- `edgePieceEquiv` as a monoid homomorphism. -/
@[simps]
def edgePieceEquivHom : PRubik →* Perm EdgePiece where
  toFun cube := cube.edgePieceEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `cornerPieceEquiv` as a monoid homomorphism. -/
@[simps]
def cornerPieceEquivHom : PRubik →* Perm CornerPiece where
  toFun cube := cube.cornerPieceEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- A Rubik's cube defines a permutation of edges. -/
def edgeEquiv : PRubik →* Perm Edge where
  toFun cube := by
    refine ⟨Quotient.lift (fun x ↦ ⟦cube.edgePieceEquiv x⟧) ?_,
      Quotient.lift (fun x ↦ ⟦(cube.edgePieceEquiv).symm x⟧) ?_, fun e ↦ ?_, fun e ↦ ?_⟩
    · intro e₁ e₂ h
      apply Quotient.sound
      obtain rfl | rfl := EdgePiece.equiv_iff.1 h
      · rfl
      · rw [cube.edge_flip]
        exact EdgePiece.flip_equiv _
    · intro e₁ e₂ h
      apply Quotient.sound
      obtain rfl | rfl := EdgePiece.equiv_iff.1 h
      · rfl
      · rw [cube.edge_flip_symm]
        exact EdgePiece.flip_equiv _
    · refine Quotient.inductionOn e ?_
      intro
      simp_rw [Quotient.lift_mk, Equiv.symm_apply_apply]
    · refine Quotient.inductionOn e ?_
      intro
      simp_rw [Quotient.lift_mk, Equiv.apply_symm_apply]
  map_one' := by
    ext e
    refine Quotient.inductionOn e ?_
    exact fun _ ↦ rfl
  map_mul' cube₁ cube₂ := by
    ext e
    refine Quotient.inductionOn e ?_
    simp

theorem edgeEquiv_mk (cube : PRubik) (e : EdgePiece) :
    edgeEquiv cube ⟦e⟧ = ⟦cube.edgePieceEquiv e⟧ :=
  rfl

/-- A Rubik's cube defines a permutation of corners. -/
def cornerEquiv : PRubik →* Perm Corner where
  toFun cube := by
    refine ⟨Quotient.lift (fun x ↦ ⟦cube.cornerPieceEquiv x⟧) ?_,
      Quotient.lift (fun x ↦ ⟦(cube.cornerPieceEquiv).symm x⟧) ?_, fun c ↦ ?_, fun c ↦ ?_⟩
    · intro e₁ e₂ h
      apply Quotient.sound
      obtain rfl | rfl | rfl := CornerPiece.equiv_iff.1 h
      · rfl
      · rw [cube.corner_cyclic]
        exact CornerPiece.cyclic_equiv _
      · rw [cube.corner_cyclic]
        exact (CornerPiece.cyclic_equiv _).symm
    · intro e₁ e₂ h
      apply Quotient.sound
      obtain rfl | rfl | rfl := CornerPiece.equiv_iff.1 h
      · rfl
      · rw [cube.corner_cyclic_symm]
        exact CornerPiece.cyclic_equiv _
      · rw [cube.corner_cyclic_symm]
        exact (CornerPiece.cyclic_equiv _).symm
    · refine Quotient.inductionOn c ?_
      intro
      simp_rw [Quotient.lift_mk, Equiv.symm_apply_apply]
    · refine Quotient.inductionOn c ?_
      intro
      simp_rw [Quotient.lift_mk, Equiv.apply_symm_apply]
  map_one' := by
    ext e
    refine Quotient.inductionOn e ?_
    exact fun _ ↦ rfl
  map_mul' cube₁ cube₂ := by
    ext e
    refine Quotient.inductionOn e ?_
    simp

theorem cornerEquiv_mk (cube : PRubik) (c : CornerPiece) :
    cornerEquiv cube ⟦c⟧ = ⟦cube.cornerPieceEquiv c⟧ :=
  rfl

/-- The total parity of a Rubik's cube is the combined parity of edge and corner permutations.

This is an invariant under any valid move. -/
def parity : PRubik →* ℤˣ :=
  (Perm.sign.comp edgeEquiv) * (Perm.sign.comp cornerEquiv)

/-- The Rubik's cube with a single edge swapped with its counterclockwise edge in the same face. -/
def swapEdges (h : IsAdjacent a b) : PRubik where
  edgePieceEquiv := (swap ⟨a, b, h⟩ ⟨a, cross a b, h.cross_left.symm⟩).trans
    (swap ⟨b, a, h.symm⟩ ⟨cross a b, a, h.cross_left⟩)
  cornerPieceEquiv := Equiv.refl _
  edge_flip := by
    revert a b
    decide
  corner_cyclic _ := rfl

/-- The parity of flipped edges in a Rubik's cube can be measured as the parity of the edge piece
permutation.

This is an invariant under any valid move. -/
def edgeFlip : PRubik →* ℤˣ :=
  Perm.sign.comp edgePieceEquivHom

/-- Flips a single edge. -/
private def flipEdgeAux (e : EdgePiece) : PRubik where
  edgePieceEquiv := swap e e.flip
  cornerPieceEquiv := Equiv.refl _
  edge_flip e' := by
    obtain rfl | he := eq_or_ne e' e
    · rw [swap_apply_right, swap_apply_left, EdgePiece.flip₂]
    · obtain rfl | he' := eq_or_ne e' e.flip
      · rw [swap_apply_right, EdgePiece.flip₂, swap_apply_left]
      · rw [swap_apply_of_ne_of_ne he he', swap_apply_of_ne_of_ne] <;>
        rwa [ne_eq, ← EdgePiece.flip_inj]
  corner_cyclic _ := rfl

/-- Flips a single edge. -/
def flipEdge (e : Edge) : PRubik :=
  Quotient.liftOn e flipEdgeAux (by
    intro e₁ e₂ h
    obtain rfl | rfl := EdgePiece.equiv_iff.1 h
    · rfl
    · ext
      · dsimp [flipEdgeAux]
        rw [swap_comm]
      · rfl)

@[simp]
theorem edgePieceEquiv_flipEdge (e : EdgePiece) :
    edgePieceEquiv (flipEdge ⟦e⟧) = swap e e.flip :=
  rfl

@[simp]
theorem cornerPieceEquiv_flipEdge (e : Edge) : cornerPieceEquiv (flipEdge e) = Equiv.refl _ := by
  refine Quotient.inductionOn e ?_
  intros
  rfl

theorem cornerPieceEquiv_value (cube : PRubik) (c : CornerPiece) (a : Axis) :
    (cube.cornerPieceEquiv c).value a =
    (cube.cornerPieceEquiv (c.withAxis a)).value a + c.value a := by
  obtain h | h | h := CornerPiece.equiv_iff.1 (CornerPiece.withAxis_equiv c a)
  · rw [h]
    conv_rhs => right; rw [← h]
    rw [CornerPiece.value_withAxis, add_zero]
  · rw [h, corner_cyclic, CornerPiece.value_cyclic, add_assoc, self_eq_add_right,
      CornerPiece.value_of_snd]
    · rfl
    · rw [← c.cyclic₃, ← h]
      simp
  · conv_lhs => rw [← h]
    rw [corner_cyclic, CornerPiece.value_cyclic, add_right_inj, CornerPiece.value_of_thd]
    rw [← h]
    simp

private theorem cornerRotationAux (cube₁ cube₂ : PRubik) (c : Corner) (a : Axis) :
    (cube₁.cornerPieceEquiv (cube₂.cornerPieceEquiv (c.toCornerPiece a))).value a
    = (cube₁.cornerPieceEquiv ((cornerEquiv cube₂ c).toCornerPiece a)).value a
    + (cube₂.cornerPieceEquiv (c.toCornerPiece a)).value a := by
  refine Quotient.inductionOn c ?_
  intro c
  dsimp [cornerEquiv_mk]
  conv_lhs => rw [cornerPieceEquiv_value]
  rw [add_left_inj, CornerPiece.withAxis_eq_of_equiv]
  exact cornerPieceEquiv_equiv _ (c.withAxis_equiv a)

/-- To calculate the amount of corner rotation mod 3, we fix an arbitrary axis (here the X axis) and
count the number of **counterclockwise** corner rotations needed to orient the pieces of the
corresponding axis to said axis.

This is an invariant under any valid move. -/
def cornerRotation : PRubik →* Multiplicative (ZMod 3) where
  toFun cube := ∏ c : Corner,
    (Multiplicative.ofAdd <| (cube.cornerPieceEquiv (c.toCornerPiece Axis.x)).value Axis.x)
  map_one' := by
    convert Finset.prod_const_one
    simp
  map_mul' cube₁ cube₂ := by
    dsimp
    simp_rw [cornerRotationAux, ofAdd_add, Finset.prod_mul_distrib, mul_left_inj]
    rw [Finset.prod_equiv (cornerEquiv cube₂)] <;>
    simp

/-- Rotates a single corner **clockwise**. -/
def rotateCornerAux (c : CornerPiece) : PRubik where
  edgePieceEquiv := Equiv.refl _
  cornerPieceEquiv := (swap c c.cyclic).trans (swap c c.cyclic.cyclic)
  edge_flip _ := rfl
  corner_cyclic := by
    revert c
    decide

/-- Rotates a single corner **clockwise**. -/
def rotateCorner (c : Corner) : PRubik :=
  Quotient.liftOn c rotateCornerAux (by decide)

/-- The **Rubik's cube invariant**. This is the combined `parity`, `edgeFlip`, and `cornerRotation`
of a Rubik's cube.

A Rubik's cube is solvable iff it lies in the kernel of this homomorphism. -/
def invariant : PRubik →* ℤˣ × ℤˣ × Multiplicative (ZMod 3) :=
  parity.prod <| edgeFlip.prod cornerRotation

/-- A constructive right inverse for the invariant. -/
def invariant_inv : ℤˣ × ℤˣ × Multiplicative (ZMod 3) → PRubik :=
  fun n ↦ (swapEdges (default : EdgePiece).isAdjacent) ^ ((1 - n.1.1) / 2) *
    (flipEdge default) ^ ((1 - n.2.1.1) / 2) * (rotateCorner default) ^ n.2.2.1

/-- The invariant is surjective. -/
theorem invariant_rightInverse : Function.RightInverse invariant_inv invariant := by
  change ∀ x, _
  decide

/-- A Rubik's cube is valid when it has invariant 1. We show that this condition is equivalent to
being solvable. -/
def IsValid (cube : PRubik) : Prop :=
  cube ∈ invariant.ker

instance : DecidablePred IsValid :=
  fun cube ↦ inferInstanceAs (Decidable (invariant cube = 1))

theorem isValid_one : IsValid 1 :=
  one_mem _

theorem IsValid.mul (h₁ : IsValid cube₁) (h₂ : IsValid cube₂) : IsValid (cube₁ * cube₂) :=
  mul_mem h₁ h₂

theorem IsValid.inv (h : IsValid cube) : IsValid cube⁻¹ :=
  inv_mem h

theorem isValid_iff :
    IsValid cube ↔ parity cube = 1 ∧ edgeFlip cube = 1 ∧ cornerRotation cube = 1 := by
  rw [IsValid, invariant]
  simp only [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one]

end PRubik

/-- The subgroup of valid Rubik's cubes, i.e. those that can be reached using only valid moves. -/
def Rubik : Subgroup PRubik :=
  PRubik.invariant.ker

namespace Rubik

/-- Construct a Rubik's cube, inferring the validity hypothesis. -/
def mk (cube : PRubik) (h : PRubik.IsValid cube := by decide) : Rubik :=
  ⟨cube, h⟩

instance : Repr Rubik :=
  ⟨fun cube ↦ reprPrec cube.1⟩

theorem isValid (cube : Rubik) : cube.1.IsValid :=
  cube.2

end Rubik
