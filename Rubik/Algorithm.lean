import Rubik.Move

open Orientation PRubik


namespace Moves
set_option maxRecDepth 1500

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
    (cornerEquiv (ofOrientation U)) (Corner.mk U B L) = Corner.mk U L F :=
  rfl

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

theorem fixCorners₃_move₁ (h₁ : c₁ ≠ c₂) (h₂ : c₁ ≠ c₃) :
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

@[simp]
theorem edgeEquiv_flipEdges : edgeEquiv (move (flipEdges e₁ e₂)) = 1 := by
  ext a
  refine a.inductionOn ?_
  intro a
  simp [edgeEquiv_mk]

/-- A sequence of moves cycling `Corner.mk U R B`, `Corner.mk U B L`, and `Corner.mk U L F`, while
fixing all edges. -/
def cycleCornersAux : Moves :=
  [R, R, D, B, B, D, D, D, F, F, D, B, B, D, D, D, F, F, R, R]

private theorem edgePieceEquiv_cycleCornersAux :
    edgePieceEquiv (move cycleCornersAux) = 1 := by
  decide

private theorem cornerEquiv_cycleCornersAux : cornerEquiv (move cycleCornersAux) =
    Equiv.cycle (Corner.mk U R B) (Corner.mk U B L) (Corner.mk U L F) := by
  decide

/-- A sequence of moves that cycles three corners, while fixing all edges. -/
def cycleCorners (c₁ c₂ c₃ : Corner) : Moves :=
  if c₁ = c₂ ∨ c₂ = c₃ ∨ c₃ = c₁ then [] else
    let m := fixCorners₃ c₁ c₂ c₃
    m ++ cycleCornersAux ++ m.symm

@[simp]
theorem edgePieceEquiv_cycleCorners (c₁ c₂ c₃ : Corner) :
    edgePieceEquiv (move (cycleCorners c₁ c₂ c₃)) = 1 := by
  rw [cycleCorners]
  split_ifs with h
  · rfl
  · simp [edgePieceEquiv_cycleCornersAux]

@[simp]
theorem cornerEquiv_cycleCorners (c₁ c₂ c₃ : Corner) :
    cornerEquiv (move (cycleCorners c₁ c₂ c₃)) = Equiv.cycle c₁ c₂ c₃ := by
  rw [cycleCorners, Equiv.cycle]
  split_ifs with h
  · simp
  · have h' := h
    simp_rw [not_or, ← ne_eq] at h'
    simp [cornerEquiv_cycleCornersAux, ← mul_assoc]
    rw [fixCorners₃_move₁ h'.1 h'.2.2.symm, fixCorners₃_move₂ _ h'.2.1, Equiv.cycle, if_neg h]

/-- A sequence of moves rotating `Corner.mk U B L` **clockwise** and, `Corner.mk U L F`
**counterclockwise**, while fixing all edges. -/
def rotateCornersAux : Moves :=
  [L, L, D, D, D, L, L, D, F, F, U, U, U, F, U, L, L, U, L, L, U, U, U, F]

private theorem edgePieceEquiv_rotateCornersAux :
    edgePieceEquiv (move rotateCornersAux) = 1 := by
  decide

private theorem cornerPieceEquiv_rotateCornersAux : cornerPieceEquiv (move rotateCornersAux) =
    (Corner.mk U B L).rotateEquiv * (Corner.mk U L F).rotateEquiv⁻¹ := by
  decide

/-- A sequence of moves that rotates `c₁` **clockwise** and `c₂` **counterclockwise**, while fixing
all edges. -/
def rotateCorners (c₁ c₂ : Corner) : Moves :=
  if c₁ = c₂ then [] else
    let m := fixCorners₂ c₁ c₂
    m ++ rotateCornersAux ++ m.symm

@[simp]
theorem edgePieceEquiv_rotateCorners (c₁ c₂ : Corner) :
    edgePieceEquiv (move (rotateCorners c₁ c₂)) = 1 := by
  rw [rotateCorners]
  split_ifs <;> simp [edgePieceEquiv_rotateCornersAux]

@[simp]
theorem cornerPieceEquiv_rotateCorners (c₁ c₂ : Corner) :
    cornerPieceEquiv (move (rotateCorners c₁ c₂)) = c₁.rotateEquiv * c₂.rotateEquiv⁻¹ := by
  rw [rotateCorners]
  split_ifs with h
  · simp [h]
  · simp [cornerPieceEquiv_rotateCornersAux, ← mul_assoc, Equiv.cycle_inv]
    congr
    · conv_rhs => rw [← fixCorners₂_move₁ h, cornerEquiv_mk, Corner.rotateEquiv_mk,
        ← corner_cyclic, ← corner_cyclic]
      rfl
    · conv_rhs => rw [← fixCorners₂_move₂ c₁ c₂, cornerEquiv_mk, Corner.rotateEquiv_mk,
        Equiv.cycle_inv, ← corner_cyclic, ← corner_cyclic]
      rfl

end Moves

namespace Rubik

/-- A sequence of moves that puts the cube's edges in their correct position, in the specified
order. -/
private def solveEdgesAux (cube : Rubik) : List Edge → Moves
  | [] => []
  | a::l =>
    let m := Moves.swapEdges a ((edgeEquiv cube).symm a)
    let cube' := cube * move m
    m ++ solveEdgesAux cube' (l.filter fun e ↦ edgeEquiv cube' e ≠ e)
termination_by l => l.length
decreasing_by exact (List.length_filter_le _ _).trans_lt (Nat.lt_succ_self _)

private theorem solveEdgesAux_edgeEquiv (cube : Rubik) (l : List Edge)
    (he : ∀ e, e ∈ l ↔ edgeEquiv cube e ≠ e) :
    edgeEquiv (PRubik.move (solveEdgesAux cube l)) = (edgeEquiv cube)⁻¹ :=
  match l with
  | [] => by simpa [solveEdgesAux, Equiv.ext_iff] using he
  | a::l => by
    rw [solveEdgesAux]
    simp
    rw [solveEdgesAux_edgeEquiv]
    · simp
    · simp
      intro e ha
      obtain rfl | he₁ := eq_or_ne e a
      · simp at ha
      · obtain rfl | he₂ := eq_or_ne e ((PRubik.edgeEquiv cube).symm a)
        · apply (List.mem_cons.1 ((he _).2 _)).resolve_left he₁
          simpa using he₁.symm
        · rw [Equiv.swap_apply_of_ne_of_ne he₁ he₂] at ha
          exact (List.mem_cons.1 ((he _).2 ha)).resolve_left he₁
termination_by l.length
decreasing_by exact (List.length_filter_le _ _).trans_lt (Nat.lt_succ_self _)

/-- A sequence of moves that puts the cube's edges in their correct position. -/
def solveEdges (cube : Rubik) : Moves :=
  solveEdgesAux cube ((Finset.univ.filter fun e ↦ edgeEquiv cube e ≠ e).sort (· ≤ ·))

@[simp]
theorem solveEdges_edgeEquiv (cube : Rubik) :
    edgeEquiv (PRubik.move (solveEdges cube)) = (edgeEquiv cube)⁻¹ := by
  apply solveEdgesAux_edgeEquiv
  simp

/-- A sequence of moves that puts the cube's edges in their correct orientation, in the specified
order. -/
private def solveEdgePiecesAux : List Edge → Moves
  | a::b::l => Moves.flipEdges a b ++ solveEdgePiecesAux l
  | _ => []

private theorem one_ne_neg_one : (1 : ℤˣ) ≠ -1 := by decide

theorem solveEdgePiecesAux_edgePieceEquiv (cube : Rubik) (hc : edgeEquiv cube = 1)
    (l : List Edge) (hl : l.Nodup) (he : ∀ e, ⟦e⟧ ∈ l ↔ edgePieceEquiv cube e ≠ e) :
    edgePieceEquiv (PRubik.move (solveEdgePiecesAux l)) = (edgePieceEquiv cube)⁻¹ :=
  have hc' (e) : cube.1.edgePieceEquiv e = e ∨ cube.1.edgePieceEquiv e = e.flip :=
    EdgePiece.equiv_iff.1 <| Quotient.exact <| Equiv.ext_iff.1 hc ⟦e⟧
  match l with
  | [] => by simpa [solveEdgePiecesAux, Equiv.ext_iff] using he
  | [a] => by
    apply (one_ne_neg_one _).elim
    conv_lhs => rw [← (Rubik.isValid cube).edgeFlip, edgeFlip, MonoidHom.coe_comp,
      Function.comp_apply, edgePieceEquivHom_apply]
    suffices edgePieceEquiv cube = a.flipEquiv by
      rw [this]
      refine a.inductionOn ?_
      simpa using fun a ↦ a.flip_ne.symm
    ext e
    simp_rw [List.mem_singleton] at he
    obtain rfl | ha := eq_or_ne a ⟦e⟧
    · rw [Edge.flipEquiv_mk, Equiv.swap_apply_left]
      exact (hc' _).resolve_left ((he _).1 rfl)
    · rwa [Edge.flipEquiv_of_ne ha, ← not_ne_iff, ← he, eq_comm]
  | a::b::l => by
    simp only [List.nodup_cons, List.mem_cons, not_or, ← ne_eq] at hl
    rw [solveEdgePiecesAux, PRubik.move_append, edgePieceEquiv_mul, Moves.edgePieceEquiv_flipEdges,
      solveEdgePiecesAux_edgePieceEquiv (cube * move (Moves.flipEdges a b)) _ _ hl.2.2]
    · simp [mul_assoc]
    · simp
      intro e
      have H (e : EdgePiece) : edgePieceEquiv cube e ≠ e ↔ (edgePieceEquiv cube e).flip = e := by
        constructor <;> intro h
        · rw [← EdgePiece.flip_inj, EdgePiece.flip₂]
          exact (hc' _).resolve_left h
        · conv_rhs => rw [← h]
          exact (EdgePiece.flip_ne _).symm
      obtain rfl | ha := eq_or_ne ⟦e⟧ a
      · rw [Edge.flipEquiv_of_ne hl.1.1.symm, Edge.flipEquiv_mk, Equiv.swap_apply_left, edge_flip,
          ← H, ← he]
        simpa using hl.1.2
      · obtain rfl | hb := eq_or_ne ⟦e⟧ b
        · rw [Edge.flipEquiv_mk, Equiv.swap_apply_left, Edge.flipEquiv_of_ne, ← ne_eq, edge_flip,
            ne_eq, ← H, ← he]
          · simpa using hl.2.1
          · rw [Edge.mk_flip]
            exact hl.1.1
        · rw [Edge.flipEquiv_of_ne hb.symm, Edge.flipEquiv_of_ne ha.symm, ← ne_eq, ← he]
          simp [ha, hb]
    · simpa

/-- A sequence of moves that puts the cube's edges in their correct orientation. -/
def solveEdgePieces (cube : Rubik) : Moves := by
  refine solveEdgePiecesAux ((Finset.univ.filter fun e : Edge ↦ e.lift
    (fun e ↦ PRubik.edgePieceEquiv cube e ≠ e) ?_).sort (· ≤ ·))
  intro e₁ e₂ h
  obtain rfl | rfl := EdgePiece.equiv_iff.1 h <;> simp

@[simp]
theorem solveEdgePieces_edgePieceEquiv (cube : Rubik) (hc : PRubik.edgeEquiv cube = 1) :
    edgePieceEquiv (PRubik.move (solveEdgePieces cube)) = (edgePieceEquiv cube)⁻¹ := by
  apply solveEdgePiecesAux_edgePieceEquiv _ hc _ (Finset.sort_nodup _ _)
  simp [edgeEquiv_mk]

/-- `other a b x` is whichever of `a` or `b` which is not equal to `x`. -/
private def other (a b x : Corner) : Corner :=
  if x = a then b else a

/-- A sequence of moves that puts the cube's corners in their correct position, in the specified
order. -/
private def solveCornersAux (cube : Rubik) : List Corner → Moves
  | a::b::c::l =>
    let x := (cornerEquiv cube).symm a
    let m := Moves.cycleCorners a x (other b c x)
    let cube' := cube * move m
    m ++ solveCornersAux cube' ((b::c::l).filter fun e ↦ cornerEquiv cube' e ≠ e)
  | [] | [_] | [_, _] => []
termination_by l => l.length
decreasing_by exact (List.length_filter_le _ _).trans_lt (Nat.lt_succ_self _)

private theorem solveCornersAux_edgePieceEquiv (cube : Rubik)
    (he : edgePieceEquiv cube = 1) (l : List Corner) :
    edgePieceEquiv (PRubik.move (solveCornersAux cube l)) = 1 :=
  match l with
  | a::b::c::l => by
    rw [solveCornersAux, PRubik.move_append, edgePieceEquiv_mul, Moves.edgePieceEquiv_cycleCorners,
      one_mul, solveCornersAux_edgePieceEquiv]
    simpa
  | [] | [_] | [_, _] => by all_goals simp [solveCornersAux]
termination_by l.length
decreasing_by exact (List.length_filter_le _ _).trans_lt (Nat.lt_succ_self _)

private theorem solveCornersAux_cornerEquiv (cube : Rubik) (he : edgePieceEquiv cube = 1)
    (l : List Corner) (hl : l.Nodup) (hc : ∀ c, c ∈ l ↔ cornerEquiv cube c ≠ c) :
    cornerEquiv (PRubik.move (solveCornersAux cube l)) = (cornerEquiv cube)⁻¹ :=
  match l with
  | [] => by simpa [solveCornersAux, Equiv.ext_iff] using hc
  | [a] => by
    simp at hc
    have ha := ((hc a).1 rfl)
    apply (ha _).elim
    have := hc ((cornerEquiv cube).symm a)
    rw [Equiv.apply_symm_apply, Equiv.eq_symm_apply] at this
    rw [← Equiv.eq_symm_apply, this.2 ha]
  | [a, b] => by
    apply (one_ne_neg_one _).elim
    conv_lhs => rw [← (Rubik.isValid cube).parity, parity, MonoidHom.mul_apply, MonoidHom.coe_comp,
      Function.comp_apply, edgeEquiv_of_edgePieceEquiv_eq_one he]
    suffices cornerEquiv cube = Equiv.swap a b by simpa [this] using hl
    rw [eq_comm]
    ext c
    obtain rfl | ha := eq_or_ne c a
    · rw [Equiv.swap_apply_left]
      have hc₁ := (hc c).1 (List.mem_cons_self _ _)
      have hc₂ := hc₁
      rw [ne_eq, ← (cornerEquiv cube).apply_eq_iff_eq, ← ne_eq, ← hc, List.mem_pair,
        eq_comm (b := b)] at hc₂
      exact hc₂.resolve_left hc₁
    · obtain rfl | hb := eq_or_ne c b
      · rw [Equiv.swap_apply_right]
        have hc₁ := (hc c).1 (List.mem_cons_of_mem _ (List.mem_singleton_self _))
        have hc₂ := hc₁
        rw [ne_eq, ← (cornerEquiv cube).apply_eq_iff_eq, ← ne_eq, ← hc, List.mem_pair,
          eq_comm (b := a)] at hc₂
        exact hc₂.resolve_right hc₁
      · rw [Equiv.swap_apply_of_ne_of_ne ha hb, ← not_ne_iff, ne_comm, ← hc]
        simp [ha, hb]
  | a::b::c::l => by
    rw [solveCornersAux]
    simp only [Subgroup.coe_mul, map_mul, PRubik.move_append]
    rw [solveCornersAux_cornerEquiv _ _ _ ((List.filter_sublist _).nodup hl.of_cons)]
    · simp
    · simp
      simp_rw [List.nodup_cons, List.mem_cons, not_or] at hl
      intro x hx
      rw [or_iff_not_imp_left, or_iff_not_imp_left]
      intro hxb hxc
      have hxo : other b c ((cornerEquiv cube).symm a) ≠ x := by
        rw [other]
        split_ifs <;> rwa [ne_comm]
      obtain rfl | hxa := eq_or_ne x a
      · rw [Equiv.cycle_fst _ hxo, Equiv.apply_symm_apply] at hx
        · cases hx rfl
        · rw [other]
          split_ifs with h
          · rw [h]
            exact hl.2.1.1
          · exact h
      · obtain rfl | hxa' := eq_or_ne x ((cornerEquiv cube).symm a)
        · have hxa' := hxa
          conv_rhs at hxa' => rw [← (cornerEquiv cube).apply_symm_apply a]
          rw [ne_comm, ← hc] at hxa'
          simpa [hxa, hxb, hxc] using hxa'
        · rw [Equiv.cycle_apply_of_ne hxa hxa' hxo.symm, ← ne_eq, ← hc] at hx
          simpa [hxa, hxb, hxc] using hx
    · simpa
termination_by l.length
decreasing_by exact (List.length_filter_le _ _).trans_lt (Nat.lt_succ_self _)

/-- A sequence of moves that puts the cube's corners in their correct position. -/
def solveCorners (cube : Rubik) : Moves :=
  solveCornersAux cube ((Finset.univ.filter fun c ↦ cornerEquiv cube c ≠ c).sort (· ≤ ·))

theorem solveCorners_edgePieceEquiv (cube : Rubik) (he : edgePieceEquiv cube = 1) :
    edgePieceEquiv (PRubik.move (solveCorners cube)) = 1 :=
  solveCornersAux_edgePieceEquiv _ he _

theorem solveCorners_cornerEquiv (cube : Rubik) (he : edgePieceEquiv cube = 1) :
    cornerEquiv (PRubik.move (solveCorners cube)) = (cornerEquiv cube)⁻¹ := by
  apply solveCornersAux_cornerEquiv _ he _ (Finset.sort_nodup _ _)
  simp

end Rubik
