import Rubik.Move

open Orientation PRubik

@[simp]
theorem Equiv.symm_mul {α : Type*} (e₁ e₂ : Equiv.Perm α) : (e₁ * e₂).symm = e₂.symm * e₁.symm :=
  rfl

namespace Moves

/-- Given two edges `e₁` and `e₂` in the same face `a`, `moveEdgeFace e₁ e₂ a` is the sequence of
moves repeating `a` until `e₂` is sent to `e₁`. See `moveEdgeFace_move`. -/
def moveEdgeFace (e₁ e₂ : Edge) (a : Orientation) : Moves :=
  let f₁ := (e₁.toEdgePiece a).snd
  let f₂ := (e₂.toEdgePiece a).snd
  List.replicate (
    if f₁ = f₂ then 0 else
    if f₁.rotate a = f₂ then 1 else
    if (f₁.rotate a).rotate a = f₂ then 2 else 3
  ) a

theorem moveEdgeFace_move : ∀ {e₁ e₂ : Edge} {a : Orientation}, a ∈ e₁.toFinset → a ∈ e₂.toFinset →
    edgeEquiv (move (moveEdgeFace e₁ e₂ a)) e₁ = e₂ := by
  decide

/-- Given two corners `c₁` and `c₂` in the same face `a`, `moveCornerFace c₁ c₂ a` is the sequence
of moves repeating `a` until `c₂` is sent to `c₁`. See `moveCornerFace_move`. -/
def moveCornerFace (c₁ c₂ : Corner) (a : Orientation) : Moves :=
  moveEdgeFace
    ⟦EdgeCornerEquiv.symm (c₁.toCornerPiece a.axis)⟧
    ⟦EdgeCornerEquiv.symm (c₂.toCornerPiece a.axis)⟧ a

theorem moveCornerFace_move : ∀ {c₁ c₂ : Corner} {a : Orientation},
    a ∈ c₁.toFinset → a ∈ c₂.toFinset → cornerEquiv (move (moveCornerFace c₁ c₂ a)) c₁ = c₂ := by
  decide

/-- A sequence of moves sending a given edge to the `D` face, guaranteeing not to move
`Edge.mk U B` (unless that's the chosen edge). -/
private def fixEdgeAux (e : Edge) : Moves × Edge :=
  if D ∈ e.toFinset then ([], e) else
  if U ∈ e.toFinset then
    let f := e.toEdgePiece U
    (List.replicate 2 f.snd, ⟦⟨-f.fst, f.snd, f.isAdjacent⟩⟧) else
  if L ∈ e.toFinset then (moveEdgeFace (Edge.mk D L) e L, Edge.mk D L) else
  (moveEdgeFace (Edge.mk D R) e R, Edge.mk D R)

/-- A sequence of moves sending a given edge to `Edge.mk U L`, guaranteeing not to move
`Edge.mk U B` (unless that's the chosen edge). -/
def fixEdge (e : Edge) : Moves :=
  let (m, e) := fixEdgeAux e
  m ++ moveEdgeFace (Edge.mk D L) e D ++ Moves.L2

@[simp]
theorem fixEdge_move : ∀ e : Edge, edgeEquiv (move (fixEdge e)) (Edge.mk U L) = e := by
  decide

theorem fixEdge_fix : ∀ {e : Edge}, e ≠ Edge.mk U B →
    edgeEquiv (move (fixEdge e)) (Edge.mk U B) = Edge.mk U B := by
  decide

/-- A sequence of moves sending `e₁` to `Edge.mk U B` and `e₂` to `Edge.mk U L`. -/
def fixEdges (e₁ e₂ : Edge) : Moves :=
  let m := fixEdge e₁ ++ Moves.U
  m ++ fixEdge ((edgeEquiv (move m)).symm e₂)

theorem fixEdges_move₁ (h : e₁ ≠ e₂) : edgeEquiv (move (fixEdges e₁ e₂)) (Edge.mk U B) = e₁ := by
  have : edgeEquiv (ofOrientation U) (Edge.mk U B) = Edge.mk U L := by decide
  simp [fixEdges]
  rw [fixEdge_fix, this, fixEdge_move]
  rwa [ne_eq, Equiv.symm_apply_eq, this, Equiv.symm_apply_eq, fixEdge_move, eq_comm]

@[simp]
theorem fixEdges_move₂ (e₁ e₂ : Edge) : edgeEquiv (move (fixEdges e₁ e₂)) (Edge.mk U L) = e₂ := by
  simp [fixEdges]

/-- A sequence of moves sending a given corner to the `D` face, guaranteeing not to move
`Corner.mk U R B` or `Corner.mk U B L` (unless that's the chosen corner). -/
private def fixCornerAux (c : Corner) : Moves × Corner :=
  if D ∈ c.toFinset then ([], c) else
  if c = Corner.mk U L F then (Moves.F2, Corner.mk D R F) else
  if c = Corner.mk U F R then (Moves.F2, Corner.mk D F L) else
  if c = Corner.mk U B L then (Moves.L2, Corner.mk D F L) else (Moves.R2, Corner.mk D R F)

/-- A sequence of moves sending a given corner to `Corner.mk U L F`, guaranteeing not to move
`Corner.mk U R B` or `Corner.mk U B L` (unless that's the chosen corner). -/
def fixCorner (c : Corner) : Moves :=
  let (m, c) := fixCornerAux c
  m ++ moveCornerFace (Corner.mk D R F) c D ++ Moves.F2

@[simp]
theorem fixCorner_move : ∀ c : Corner, cornerEquiv (move (fixCorner c)) (Corner.mk U L F) = c := by
  decide

theorem fixCorner_fix₁ : ∀ {c : Corner}, c ≠ Corner.mk U R B →
    cornerEquiv (move (fixCorner c)) (Corner.mk U R B) = Corner.mk U R B := by
  decide

theorem fixCorner_fix₂ : ∀ {c : Corner}, c ≠ Corner.mk U B L →
    cornerEquiv (move (fixCorner c)) (Corner.mk U B L) = Corner.mk U B L := by
  decide
--`Corner.mk U R B`
/-- A sequence of moves sending `c₁` to `Corner.mk U B L` and `c₂` to `Corner.mk U L F`. -/
def fixCorners₂ (c₁ c₂ : Corner) : Moves :=
  let m := fixCorner c₁ ++ Moves.U
  m ++ fixCorner ((cornerEquiv (move m)).symm c₂)
  /-let m := fixCorner c₁ ++ Moves.U
  let n := fixCorner ((cornerEquiv (move m)).symm c₂) ++ Moves.U
  let p := m ++ n
  p ++ fixCorner ((cornerEquiv (move p)).symm c₃)-/

private theorem cornerEquiv_UBL :
    (cornerEquiv (ofOrientation U)) (Corner.mk U B L) = Corner.mk U L F := by
  decide

theorem fixCorners₂_move₁ (h : c₁ ≠ c₂) :
    cornerEquiv (move (fixCorners₂ c₁ c₂)) (Corner.mk U B L) = c₁ := by
  simp [fixCorners₂]
  rw [fixCorner_fix₂, cornerEquiv_UBL, fixCorner_move]
  rwa [ne_eq, Equiv.symm_apply_eq, cornerEquiv_UBL, Equiv.symm_apply_eq, fixCorner_move, eq_comm]

@[simp]
theorem fixCorners₂_move₂ (c₁ c₂ : Corner) :
    cornerEquiv (move (fixCorners₂ c₁ c₂)) (Corner.mk U L F) = c₂ := by
  simp [fixCorners₂]

/-- A sequence of moves sending `c₁` to `Corner.mk U R B`, `c₂` to `Corner.mk U B L`, and `c₃` to
`Corner.mk U L F`. -/
def fixCorners₃ (c₁ c₂ c₃ : Corner) : Moves :=
  let m := fixCorners₂ c₁ c₂ ++ Moves.U
  m ++ fixCorner ((cornerEquiv (move m)).symm c₃)

theorem fixCorners_move₁ (h₁ : c₁ ≠ c₂) (h₂ : c₁ ≠ c₃) :
    cornerEquiv (move (fixCorners₃ c₁ c₂ c₃)) (Corner.mk U R B) = c₁ := by
  have : (cornerEquiv (ofOrientation U)) (Corner.mk U R B) = Corner.mk U B L := by decide
  simp [fixCorners₃]
  rw [fixCorner_fix₁, this, fixCorners₂_move₁ h₁]
  rwa [ne_eq, Equiv.symm_apply_eq, this, Equiv.symm_apply_eq, fixCorners₂_move₁ h₁, eq_comm]

theorem fixCorners₃_move₂ (c₁ : Corner) (h : c₂ ≠ c₃) :
    cornerEquiv (move (fixCorners₃ c₁ c₂ c₃)) (Corner.mk U B L) = c₂ := by
  simp [fixCorners₃]
  rw [fixCorner_fix₂, cornerEquiv_UBL, fixCorners₂_move₂]
  rwa [ne_eq, Equiv.symm_apply_eq, cornerEquiv_UBL, Equiv.symm_apply_eq, fixCorners₂_move₂, eq_comm]

theorem fixCorners₃_move₃ (c₁ c₂ c₃ : Corner) :
    cornerEquiv (move (fixCorners₃ c₁ c₂ c₃)) (Corner.mk U L F) = c₃ := by
  simp [fixCorners₃]

/-- A sequence of moves that swaps `Edge.mk U B` and `Edge.mk U L`. All other edges are fixed, but
some corners are moved. -/
private def swapEdgesAux : Moves :=
  [F, U, F, F, F, U, F, U, U, F, F, F, U]

set_option maxRecDepth 750 in
private theorem edgeEquiv_swapEdgesAux :
    edgeEquiv (move swapEdgesAux) = Equiv.swap (Edge.mk U B) (Edge.mk U L) := by
  decide

/-- A sequence of moves that swaps two edges. All other edges are fixed, but some corners are
moved. -/
def swapEdges (e₁ e₂ : Edge) : Moves :=
  let m := fixEdges e₁ e₂
  m.symm ++ swapEdgesAux ++ m

theorem edgeEquiv_swapEdges (h : e₁ ≠ e₂) :
    edgeEquiv (move (swapEdges e₁ e₂)) = Equiv.swap e₁ e₂ := by
  simp [swapEdges, edgeEquiv_swapEdgesAux]
  ext e
  obtain rfl | h := eq_or_ne e (Edge.mk U B)
  · simp
    rw [fixEdges_]

end Moves
