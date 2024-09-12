import Rubik.PRubik

protected theorem EdgePiece.card : Fintype.card EdgePiece = 24 :=
  rfl

protected theorem Edge.card : Fintype.card Edge = 12 :=
  rfl

protected theorem CornerPiece.card : Fintype.card CornerPiece = 24 :=
  rfl

protected theorem Corner.card : Fintype.card Corner = 8 :=
  rfl
