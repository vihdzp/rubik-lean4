import Rubik.Move

open Orientation PRubik


namespace Moves
set_option maxRecDepth 1000

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

/-- A sequence of moves sending `c₁` to `Corner.mk U B L` and `c₂` to `Corner.mk U L F`. -/
def fixCorners₂ (c₁ c₂ : Corner) : Moves :=
  let m := fixCorner c₁ ++ Moves.U
  m ++ fixCorner ((cornerEquiv (move m)).symm c₂)

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

@[simp]
theorem fixCorners₃_move₃ (c₁ c₂ c₃ : Corner) :
    cornerEquiv (move (fixCorners₃ c₁ c₂ c₃)) (Corner.mk U L F) = c₃ := by
  simp [fixCorners₃]

/-- A sequence of moves that swaps `Edge.mk U B` and `Edge.mk U L`. All other edges are fixed, but
some corners are moved. -/
private def swapEdgesAux : Moves :=
  [F, U, F, F, F, U, F, U, U, F, F, F, U]

private theorem edgeEquiv_swapEdgesAux :
    edgeEquiv (move swapEdgesAux) = Equiv.swap (Edge.mk U B) (Edge.mk U L) := by
  decide

/-- A sequence of moves that swaps two edges. All other edges are fixed, but some corners are
moved. -/
def swapEdges (e₁ e₂ : Edge) : Moves :=
  if e₁ = e₂ then [] else
    let m := fixEdges e₁ e₂
    m ++ swapEdgesAux ++ m.symm

@[simp]
theorem edgeEquiv_swapEdges : edgeEquiv (move (swapEdges e₁ e₂)) = Equiv.swap e₁ e₂ := by
  rw [swapEdges]
  split_ifs with h
  · rw [h, Equiv.swap_self, move_nil, edgeEquiv_one]
    rfl
  · simp [edgeEquiv_swapEdgesAux, ← mul_assoc, fixEdges_move₁ h]

/-- A sequence of moves that flips `Edge.mk U B` and `Edge.mk U L`. All other edges are fixed, but
some corners are moved. -/
private def flipEdgesAux : Moves :=
  [B, U, B, B, B, U, B, B, B, R, B, R, R, R, B, U, U, B, B, B]

private theorem edgePieceEquiv_flipEdgesAux :
    edgePieceEquiv (move flipEdgesAux) = (Edge.mk U B).flipEquiv * (Edge.mk U L).flipEquiv := by
  decide

/-- A sequence of moves that flips two edges. All other edges are fixed, but some corners are
moved. -/
def flipEdges (e₁ e₂ : Edge) : Moves :=
  if e₁ = e₂ then [] else
    let m := fixEdges e₁ e₂
    m ++ flipEdgesAux ++ m.symm

@[simp]
theorem edgePieceEquiv_flipEdges :
    edgePieceEquiv (move (flipEdges e₁ e₂)) = e₁.flipEquiv * e₂.flipEquiv := by
  rw [flipEdges]
  split_ifs with h
  · rw [h, move_nil, edgePieceEquiv_one]
    refine e₂.inductionOn ?_
    intro e₂
    rw [Edge.flipEquiv_mk, Equiv.swap_mul_self]
  · simp [edgePieceEquiv_flipEdgesAux, ← mul_assoc]
    congr
    · conv_rhs => rw [← fixEdges_move₁ h, edgeEquiv_mk, Edge.flipEquiv_mk, ← edge_flip]
      rfl
    · conv_rhs => rw [← fixEdges_move₂ e₁ e₂, edgeEquiv_mk, Edge.flipEquiv_mk, ← edge_flip]
      rfl

end Moves

namespace Rubik

/-- A sequence of moves that puts the cube's edges in their correct position, in the specified
order. -/
private def solveEdgesAux (cube : Rubik) (l : List Edge) (hn : l.Nodup)
    (he : ∀ e, e ∈ l ↔ PRubik.edgeEquiv cube e ≠ e) : Moves :=
  match l with
  | [] => []
  | a::l =>
    let m := Moves.swapEdges a ((PRubik.edgeEquiv cube).symm a)
    let c := cube * move m
    m ++ solveEdgesAux c (l.filter fun e ↦ PRubik.edgeEquiv c e ≠ e) (by
      sorry
    ) (by
      intro e
      simp [c, m, Rubik.move]
      intro ha
      obtain rfl | he₁ := eq_or_ne e a
      · simp at ha
      · obtain rfl | he₂ := eq_or_ne e ((PRubik.edgeEquiv cube).symm a)
        · apply (List.mem_cons.1 ((he _).2 _)).resolve_left he₁
          simpa using he₁.symm
        · rw [Equiv.swap_apply_of_ne_of_ne he₁ he₂] at ha
          exact (List.mem_cons.1 ((he _).2 ha)).resolve_left he₁
    )
termination_by l.length
decreasing_by exact (List.length_filter_le _ _).trans_lt (Nat.lt_succ_self _)


private theorem solveEdgesAux_solve (cube : Rubik) (l : List Edge) (hn : l.Nodup)
    (he : ∀ e, e ∈ l ↔ PRubik.edgeEquiv cube e ≠ e) :
    PRubik.edgeEquiv (cube * move (solveEdgesAux cube l hn he)) = Equiv.refl _ :=
  sorry

/-- A sequence of moves that puts the cube's edges in their correct position. -/
def solveEdges (cube : Rubik) : Moves :=
  solveEdgesAux cube ((Finset.univ.filter fun e ↦ PRubik.edgeEquiv cube e ≠ e).sort (· ≤ ·))
    (Finset.sort_nodup _ _) (by simp)

theorem solveEdges_solve (cube : Rubik) :
    PRubik.edgeEquiv (cube * move (solveEdges cube)) = Equiv.refl _ :=
  solveEdgesAux_solve _ _ _ _

end Rubik
