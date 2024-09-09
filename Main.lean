import Rubik.Piece

open Orientation

/-- A pre-Rubik's cube. We represent this as a permutation of the edge pieces, and a permutation of
the corner pieces, such that pieces in the same edge or corner get mapped to the same edge or
corner.

This can be thought as the type of Rubik's cubes that can be physically assembled, without regard
for the solvability invariants. -/
structure PRubik : Type where
  /-- Returns the edge piece at a given location. -/
  edgePieceEquiv : Equiv.Perm EdgePiece
  /-- Returns the corner piece at a given location. -/
  cornerPieceEquiv : Equiv.Perm CornerPiece
  /-- Pieces in the same edge get mapped to pieces in the same edge. -/
  edge_swap (e : EdgePiece) : edgePieceEquiv e.swap = (edgePieceEquiv e).swap
  /-- Pieces in the same corner get mapped to pieces in the same corner. -/
  corner_cyclic (c : CornerPiece) : cornerPieceEquiv c.cyclic = (cornerPieceEquiv c).cyclic

attribute [simp] PRubik.edge_swap PRubik.corner_cyclic

namespace PRubik

deriving instance DecidableEq, Fintype for PRubik

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

/-- An auxiliary function to get an edge piece in a cube, inferring the adjacency hypothesis. -/
def edgePiece (cube : PRubik) (a b : Orientation) (h : IsAdjacent a b := by decide) : EdgePiece :=
  cube.edgePieceEquiv (EdgePiece.mk a b h)

/-- An auxiliary function to get a corner piece in a cube, inferring the adjacency hypothesis. -/
def cornerPiece (cube : PRubik) (a b c : Orientation) (h : IsAdjacent₃ a b c := by decide) :
    CornerPiece :=
  cube.cornerPieceEquiv (CornerPiece.mk a b c h)

/-- A list with all non-equivalent edges. This is an auxiliary function for the `PRubik.Repr` instance. -/
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

/-- A solved Rubik's cube. -/
@[simps]
protected def id : PRubik where
  edgePieceEquiv := Equiv.refl _
  cornerPieceEquiv := Equiv.refl _
  edge_swap _ := rfl
  corner_cyclic _ := rfl

instance : Inhabited PRubik := ⟨PRubik.id⟩

/-- The composition of two Rubik's cubes is the Rubik's cube where the second's scramble is
performed after the first's.

Note that this is opposite to the usual convention for function composition. -/
@[simps]
protected def trans (cube₁ cube₂ : PRubik) : PRubik where
  edgePieceEquiv := cube₂.edgePieceEquiv.trans cube₁.edgePieceEquiv
  cornerPieceEquiv := cube₂.cornerPieceEquiv.trans cube₁.cornerPieceEquiv
  edge_swap _ := by
    dsimp
    rw [cube₂.edge_swap, cube₁.edge_swap]
  corner_cyclic _ := by
    dsimp
    rw [cube₂.corner_cyclic, cube₁.corner_cyclic]

@[simp]
theorem id_trans (cube : PRubik) : PRubik.id.trans cube = cube := by
  apply PRubik.ext <;>
  intros <;>
  rfl

@[simp]
theorem trans_id (cube : PRubik) : cube.trans PRubik.id = cube := by
  apply PRubik.ext <;>
  intros <;>
  rfl

theorem trans_assoc (cube₁ cube₂ cube₃ : PRubik) :
    (cube₁.trans cube₂).trans cube₃ = cube₁.trans (cube₂.trans cube₃) := by
  apply PRubik.ext <;>
  intros <;>
  rfl

theorem edge_swap_symm (cube : PRubik) (e : EdgePiece) :
    cube.edgePieceEquiv.symm e.swap = (cube.edgePieceEquiv.symm e).swap := by
  conv_rhs => rw [← cube.edgePieceEquiv.symm_apply_apply (EdgePiece.swap _)]
  rw [cube.edge_swap, Equiv.apply_symm_apply]

theorem corner_cyclic_symm (cube : PRubik) (c : CornerPiece) :
    cube.cornerPieceEquiv.symm c.cyclic = (cube.cornerPieceEquiv.symm c).cyclic := by
  conv_rhs => rw [← cube.cornerPieceEquiv.symm_apply_apply (CornerPiece.cyclic _)]
  rw [cube.corner_cyclic, Equiv.apply_symm_apply]

/-- The inverse of a Rubik's cube is obtained by performing its moves backwards. -/
@[simps]
protected def symm (cube : PRubik) : PRubik where
  edgePieceEquiv := cube.edgePieceEquiv.symm
  cornerPieceEquiv := cube.cornerPieceEquiv.symm
  edge_swap := cube.edge_swap_symm
  corner_cyclic := cube.corner_cyclic_symm

@[simp]
theorem trans_symm (cube : PRubik) : cube.trans cube.symm = PRubik.id := by
  apply PRubik.ext <;>
  intros <;>
  simp

@[simp]
theorem symm_trans (cube : PRubik) : cube.symm.trans cube = PRubik.id := by
  apply PRubik.ext <;>
  intros <;>
  simp

/-- The "pre-Rubik's cube" group. This isn't the true Rubik's cube group as it contains positions
that are unreachable by valid moves. -/
instance : Group PRubik where
  one := PRubik.id
  mul := PRubik.trans
  mul_assoc := trans_assoc
  one_mul := id_trans
  mul_one := trans_id
  inv := PRubik.symm
  inv_mul_cancel := symm_trans

/-- Applies a **counterclockwise** rotation to an edge piece. -/
private def rotate_edgePiece (r : Orientation) : EdgePiece → EdgePiece :=
  fun e ↦ if r ∈ e.toFinset then ⟨_, _, e.isAdjacent.rotate r⟩ else e

theorem rotate_edgePiece₄ : ∀ r : Orientation, (rotate_edgePiece r)^[4] = id := by
  decide

/-- Applies a **counterclockwise** rotation to a corner piece. -/
private def rotate_cornerPiece (r : Orientation) : CornerPiece → CornerPiece :=
  fun c ↦ if r ∈ c.toFinset then ⟨_, _, _, c.isAdjacent₃.rotate r⟩ else c

theorem rotate_cornerPiece₄ : ∀ r : Orientation, (rotate_cornerPiece r)^[4] = id := by
  decide

/-- Defines the Rubik's cube where only a single **clockwise** move in a given orientation is
performed. -/
def ofOrientation (r : Orientation) : PRubik where
  edgePieceEquiv := ⟨
      rotate_edgePiece r,
      (rotate_edgePiece r)^[3],
      funext_iff.1 (rotate_edgePiece₄ r),
      funext_iff.1 (rotate_edgePiece₄ r)⟩
  cornerPieceEquiv := ⟨
      rotate_cornerPiece r,
      (rotate_cornerPiece r)^[3],
      funext_iff.1 (rotate_cornerPiece₄ r),
      funext_iff.1 (rotate_cornerPiece₄ r)⟩
  edge_swap e := by
    dsimp
    simp_rw [rotate_edgePiece, EdgePiece.swap_toFinset]
    split <;>
    rfl
  corner_cyclic c := by
    dsimp
    simp_rw [rotate_cornerPiece, CornerPiece.cyclic_toFinset]
    split <;>
    rfl

/-- Applies a clockwise rotation to a Rubik's cube. -/
def rotate (cube : PRubik) (r : Orientation) : PRubik :=
  cube.trans (ofOrientation r)

/-- A Rubik's cube defines a permutation of edges. -/
@[simps]
def edgeEquiv (cube : PRubik) : Edge ≃ Edge where
  toFun := Quotient.lift (fun x ↦ ⟦cube.edgePieceEquiv x⟧) (by
    intro e₁ e₂ h
    apply Quotient.sound
    obtain rfl | rfl := EdgePiece.equiv_iff.1 h
    · rfl
    · rw [cube.edge_swap]
      exact EdgePiece.equiv_swap _)
  invFun := Quotient.lift (fun x ↦ ⟦cube.edgePieceEquiv.symm x⟧) (by
    intro e₁ e₂ h
    apply Quotient.sound
    obtain rfl | rfl := EdgePiece.equiv_iff.1 h
    · rfl
    · rw [cube.edge_swap_symm]
      exact EdgePiece.equiv_swap _)
  left_inv e := by
    refine Quotient.inductionOn e ?_
    intro e
    simp_rw [Quotient.lift_mk, Equiv.symm_apply_apply]
  right_inv e := by
    refine Quotient.inductionOn e ?_
    intro e
    simp_rw [Quotient.lift_mk, Equiv.apply_symm_apply]

/-- A Rubik's cube defines a permutation of corners. -/
@[simps]
def cornerEquiv (cube : PRubik) : Corner ≃ Corner where
  toFun := Quotient.lift (fun x ↦ ⟦cube.cornerPieceEquiv x⟧) (by
    intro e₁ e₂ h
    apply Quotient.sound
    obtain rfl | rfl | rfl := CornerPiece.equiv_iff.1 h
    · rfl
    · rw [cube.corner_cyclic]
      exact CornerPiece.equiv_cyclic _
    · rw [cube.corner_cyclic]
      exact (CornerPiece.equiv_cyclic _).symm)
  invFun := Quotient.lift (fun x ↦ ⟦cube.cornerPieceEquiv.symm x⟧) (by
    intro e₁ e₂ h
    apply Quotient.sound
    obtain rfl | rfl | rfl := CornerPiece.equiv_iff.1 h
    · rfl
    · rw [cube.corner_cyclic_symm]
      exact CornerPiece.equiv_cyclic _
    · rw [cube.corner_cyclic_symm]
      exact (CornerPiece.equiv_cyclic _).symm)
  left_inv e := by
    refine Quotient.inductionOn e ?_
    intro e
    simp_rw [Quotient.lift_mk, Equiv.symm_apply_apply]
  right_inv e := by
    refine Quotient.inductionOn e ?_
    intro e
    simp_rw [Quotient.lift_mk, Equiv.apply_symm_apply]

end PRubik

/-- A sequence of moves to be applied to a Rubik's cube. -/
def Moves : Type := List Orientation

namespace Moves

instance : EmptyCollection Moves :=
  inferInstanceAs (EmptyCollection (List Orientation))

instance : Append Moves :=
  inferInstanceAs (Append (List Orientation))

/-- Turn right face. -/
def R : Moves := [Orientation.R]
/-- Turn up face. -/
def U : Moves := [Orientation.U]
/-- Turn front face. -/
def F : Moves := [Orientation.F]

/-- Turn left face. -/
def L : Moves := [Orientation.L]
/-- Turn down face. -/
def D : Moves := [Orientation.D]
/-- Turn back face. -/
def B : Moves := [Orientation.D]

/-- Turn right face twice. -/
def R2 : Moves := R ++ R
/-- Turn up face twice. -/
def U2 : Moves := U ++ U
/-- Turn front face twice. -/
def F2 : Moves := F ++ F

/-- Turn left face twice. -/
def L2 : Moves := L ++ L
/-- Turn down face twice. -/
def D2 : Moves := D ++ D
/-- Turn back face twice. -/
def B2 : Moves := B ++ B

/-- Turn right face backwards. -/
def R' : Moves := R2 ++ R
/-- Turn up face backwards. -/
def U' : Moves := U2 ++ U
/-- Turn front face backwards. -/
def F' : Moves := F2 ++ F

/-- Turn left face backwards. -/
def L' : Moves := L2 ++ L
/-- Turn down face backwards. -/
def D' : Moves := D2 ++ D
/-- Turn back face backwards. -/
def B' : Moves := B2 ++ B

end Moves

namespace PRubik

/-- Applies a sequence of moves to a Rubik's cube. -/
def move (cube : PRubik) (m : Moves) : PRubik :=
  m.foldl PRubik.rotate cube

theorem move_append (cube : PRubik) (m n : Moves) : cube.move (m ++ n) = (cube.move m).move n :=
  List.foldl_append _ _ _ _

end PRubik

#eval PRubik.id.move [U, R, R, F, B, R, B, B, R, U, U, L, B, B, R, U, U, U, D, D, D, R, R,
  F, R, R, R, L, B, B, U, U, F, F]
