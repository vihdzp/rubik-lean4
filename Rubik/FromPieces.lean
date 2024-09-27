import Batteries.Data.Vector.Basic
import Rubik.PRubik

/-!
We implement convenient functions `Stickers.toPRubik` and `Stickers.toRubik` to construct a Rubik's
cube from only the sticker arrangements, automatically inferring all of the relevant proofs.

This is where we also implement the `Repr` instance on `PRubik` and `Rubik`.
-/

/-- The list of stickers in a Rubik's cube. These should be given in the same order as the infoview,
omitting the centers. That is:

```
         00 01 02
         03    04
         05 06 07
08 09 10 16 17 18 24 25 26
11    12 19    20 27    28
13 14 15 21 22 23 29 30 31
         32 33 34
         35    36
         37 38 39
         40 41 42
         43    44
         45 46 47
```
-/
def Stickers : Type := Batteries.Vector Orientation 48

namespace Stickers
open Orientation

instance : GetElem Stickers ℕ Orientation fun _ i => i < 48 :=
  inferInstanceAs (GetElem (Batteries.Vector Orientation 48) _ _ _)

open Std.Format in
instance : Repr Stickers := ⟨fun c _ ↦ let space := text "⬛⬛⬛"
                       space ++ c[0]  ++ c[1]  ++ c[2]  ++ space ++ line
                    ++ space ++ c[3]  ++   U   ++ c[4]  ++ space ++ line
                    ++ space ++ c[5]  ++ c[6]  ++ c[7]  ++ space ++ line
  ++ c[8]  ++ c[9]  ++ c[10] ++ c[16] ++ c[17] ++ c[18] ++ c[24] ++ c[25] ++ c[26] ++ line
  ++ c[11] ++   L   ++ c[12] ++ c[19] ++   F   ++ c[20] ++ c[27] ++   R   ++ c[28] ++ line
  ++ c[13] ++ c[14] ++ c[15] ++ c[21] ++ c[22] ++ c[23] ++ c[29] ++ c[30] ++ c[31] ++ line
                    ++ space ++ c[32] ++ c[33] ++ c[34] ++ space ++ line
                    ++ space ++ c[35] ++   D   ++ c[36] ++ space ++ line
                    ++ space ++ c[37] ++ c[38] ++ c[39] ++ space ++ line
                    ++ space ++ c[40] ++ c[41] ++ c[42] ++ space ++ line
                    ++ space ++ c[43] ++   B   ++ c[44] ++ space ++ line
                    ++ space ++ c[45] ++ c[46] ++ c[47] ++ space⟩

/-- The stickers in a solved Rubik's cube. -/
def Solved : Stickers :=
  #v[
    U, U, U, U, U, U, U, U,
    L, L, L, L, L, L, L, L,
    F, F, F, F, F, F, F, F,
    R, R, R, R, R, R, R, R,
    D, D, D, D, D, D, D, D,
    B, B, B, B, B, B, B, B
  ]

/-- Returns the orientations associated to each edge piece. -/
def edgeOrientations (l : Stickers) : EdgePiece → Orientation × Orientation
  | .mk (true, Axis.y)  (false, Axis.z) _ => (l[1],  l[46])
  | .mk (true, Axis.y)  (false, Axis.x) _ => (l[3],  l[9])
  | .mk (true, Axis.y)  (true, Axis.x)  _ => (l[4],  l[25])
  | .mk (true, Axis.y)  (true, Axis.z)  _ => (l[6],  l[17])
  | .mk (false, Axis.x) (true, Axis.y)  _ => (l[9],  l[3])
  | .mk (false, Axis.x) (false, Axis.z) _ => (l[11], l[43])
  | .mk (false, Axis.x) (true, Axis.z)  _ => (l[12], l[19])
  | .mk (false, Axis.x) (false, Axis.y) _ => (l[14], l[35])
  | .mk (true, Axis.z)  (true, Axis.y)  _ => (l[17], l[6])
  | .mk (true, Axis.z)  (false, Axis.x) _ => (l[19], l[12])
  | .mk (true, Axis.z)  (true, Axis.x)  _ => (l[20], l[27])
  | .mk (true, Axis.z)  (false, Axis.y) _ => (l[22], l[33])
  | .mk (true, Axis.x)  (true, Axis.y)  _ => (l[25], l[4])
  | .mk (true, Axis.x)  (true, Axis.z)  _ => (l[27], l[20])
  | .mk (true, Axis.x)  (false, Axis.z) _ => (l[28], l[44])
  | .mk (true, Axis.x)  (false, Axis.y) _ => (l[30], l[33])
  | .mk (false, Axis.y) (true, Axis.z)  _ => (l[33], l[22])
  | .mk (false, Axis.y) (false, Axis.x) _ => (l[35], l[14])
  | .mk (false, Axis.y) (true, Axis.x)  _ => (l[36], l[27])
  | .mk (false, Axis.y) (false, Axis.z) _ => (l[38], l[41])
  | .mk (false, Axis.z) (false, Axis.y) _ => (l[41], l[38])
  | .mk (false, Axis.z) (false, Axis.x) _ => (l[43], l[11])
  | .mk (false, Axis.z) (true, Axis.x)  _ => (l[44], l[28])
  | .mk (false, Axis.z) (true, Axis.y)  _ => (l[46], l[1])

/-- Returns the orientations associated to each corner piece. -/
def cornerOrientations (l : Stickers) : CornerPiece → Orientation × Orientation × Orientation
  | .mk (true, Axis.y)  (false, Axis.z) _ _ => (l[0],  l[45], l[8])
  | .mk (true, Axis.y)  (false, Axis.x) _ _ => (l[5],  l[10], l[16])
  | .mk (true, Axis.y)  (true, Axis.x)  _ _ => (l[2],  l[26], l[47])
  | .mk (true, Axis.y)  (true, Axis.z)  _ _ => (l[7],  l[18], l[24])
  | .mk (false, Axis.x) (true, Axis.y)  _ _ => (l[8],  l[0],  l[45])
  | .mk (false, Axis.x) (false, Axis.z) _ _ => (l[13], l[40], l[37])
  | .mk (false, Axis.x) (true, Axis.z)  _ _ => (l[10], l[16], l[5])
  | .mk (false, Axis.x) (false, Axis.y) _ _ => (l[15], l[32], l[21])
  | .mk (true, Axis.z)  (true, Axis.y)  _ _ => (l[16], l[5],  l[10])
  | .mk (true, Axis.z)  (false, Axis.x) _ _ => (l[21], l[15], l[32])
  | .mk (true, Axis.z)  (true, Axis.x)  _ _ => (l[18], l[24], l[7])
  | .mk (true, Axis.z)  (false, Axis.y) _ _ => (l[23], l[34], l[29])
  | .mk (true, Axis.x)  (true, Axis.y)  _ _ => (l[24], l[7],  l[18])
  | .mk (true, Axis.x)  (true, Axis.z)  _ _ => (l[29], l[23], l[34])
  | .mk (true, Axis.x)  (false, Axis.z) _ _ => (l[26], l[47], l[2])
  | .mk (true, Axis.x)  (false, Axis.y) _ _ => (l[31], l[39], l[42])
  | .mk (false, Axis.y) (true, Axis.z)  _ _ => (l[32], l[21], l[15])
  | .mk (false, Axis.y) (false, Axis.x) _ _ => (l[37], l[13], l[40])
  | .mk (false, Axis.y) (true, Axis.x)  _ _ => (l[34], l[29], l[23])
  | .mk (false, Axis.y) (false, Axis.z) _ _ => (l[39], l[42], l[31])
  | .mk (false, Axis.z) (false, Axis.y) _ _ => (l[40], l[37], l[13])
  | .mk (false, Axis.z) (false, Axis.x) _ _ => (l[45], l[8],  l[0])
  | .mk (false, Axis.z) (true, Axis.x)  _ _ => (l[42], l[31], l[39])
  | .mk (false, Axis.z) (true, Axis.y)  _ _ => (l[47], l[2],  l[26])

/-- A predicate for the property that the pieces represented by the stickers all satisfy their
relevant adjacency properties, i.e. the pieces are the ones you'd actually encounter in a Rubik's
cube. -/
def IsAdjacent (l : Stickers) : Prop :=
  (∀ e : EdgePiece, let x := edgeOrientations l e; Orientation.IsAdjacent x.1 x.2) ∧
  (∀ c : CornerPiece, let x := cornerOrientations l c; Orientation.IsAdjacent₃ x.1 x.2.1 x.2.2)

instance : DecidablePred IsAdjacent :=
  inferInstanceAs (DecidablePred (fun _ ↦ _ ∧ _))

theorem isAdjacent_solved : IsAdjacent Solved := by
  decide

/-- The function mapping edge pieces to edge pieces defined by the stickers. -/
def edgePieces (l : Stickers) (h : IsAdjacent l) (e : EdgePiece) : EdgePiece :=
  let x := edgeOrientations l e; ⟨x.1, x.2, h.1 _⟩

/-- The function mapping corner pieces to corner pieces defined by the stickers. -/
def cornerPieces (l : Stickers) (h : IsAdjacent l) (c : CornerPiece) : CornerPiece :=
  let x := cornerOrientations l c; ⟨x.1, x.2.1, x.2.2, h.2 _⟩

/-- The list of stickers represents those for a `PRubik`. -/
def IsProper (l : Stickers) : Prop :=
  ∃ h : IsAdjacent l,
    Function.Surjective (edgePieces l h) ∧
    Function.Surjective (cornerPieces l h) ∧
    (∀ e, edgePieces l h e.flip = (edgePieces l h e).flip) ∧
    (∀ c, cornerPieces l h c.cyclic = (cornerPieces l h c).cyclic)

theorem IsProper.isAdjacent (h : IsProper l) : IsAdjacent l := by
  obtain ⟨h, _⟩ := h
  exact h

instance : DecidablePred IsProper :=
  inferInstanceAs (DecidablePred (fun _ ↦ ∃ _, _))

theorem isProper_solved : IsProper Solved :=
  ⟨isAdjacent_solved, by decide⟩

/-- Construct a `PRubik` from a set of stickers, inferring the necessary hypotheses. -/
def toPRubik (l : Stickers) (h : IsProper l := by decide) : PRubik := by
  refine
    ⟨⟨edgePieces l ?_, Fintype.bijInv ?_,
      Fintype.leftInverse_bijInv _, Fintype.rightInverse_bijInv _⟩,
    ⟨cornerPieces l ?_, Fintype.bijInv ?_,
      Fintype.leftInverse_bijInv _, Fintype.rightInverse_bijInv _⟩, ?_, ?_⟩ <;>
  obtain ⟨_, _, _, _, _⟩ := h
  assumption'
  all_goals
    refine (Fintype.bijective_iff_surjective_and_card _).2 ⟨?_, rfl⟩
    assumption

/-- Construct a `Rubik` from a set of stickers, inferring the necessary hypotheses. -/
def toRubik (l : Stickers) (h : IsProper l := by decide)
    (hc : PRubik.IsValid (toPRubik l h) := by decide) : Rubik :=
  ⟨toPRubik l h, hc⟩

end Stickers

namespace PRubik

def toStickers (cube : PRubik) : Stickers :=
  sorry

theorem toStickers_isProper (cube : PRubik) : cube.toStickers.IsProper :=
  sorry

instance : Repr PRubik :=
  ⟨fun c ↦ reprPrec c.toStickers⟩

end PRubik

namespace Rubik

def toStickers (cube : Rubik) : Stickers :=
  cube.1.toStickers

theorem toStickers_isProper (cube : Rubik) : (toStickers cube).IsProper :=
  cube.1.toStickers_isProper

instance : Repr Rubik :=
  ⟨fun c ↦ reprPrec c.1⟩

end PRubik
