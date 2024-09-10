import Rubik.PRubik

namespace PRubik

/-- Applies a **counterclockwise** rotation to an edge piece. -/
private def rotate_edgePiece (r : Orientation) : EdgePiece → EdgePiece :=
  fun e ↦ if r ∈ e.toFinset then ⟨_, _, e.isAdjacent.rotate r⟩ else e

private theorem rotate_edgePiece₄ : ∀ r : Orientation, (rotate_edgePiece r)^[4] = id := by
  decide

/-- Applies a **counterclockwise** rotation to a corner piece. -/
private def rotate_cornerPiece (r : Orientation) : CornerPiece → CornerPiece :=
  fun c ↦ if r ∈ c.toFinset then ⟨_, _, _, c.isAdjacent₃.rotate r⟩ else c

private theorem rotate_cornerPiece₄ : ∀ r : Orientation, (rotate_cornerPiece r)^[4] = id := by
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

@[simp]
theorem ofOrientation_inj : ∀ {r₁ r₂}, ofOrientation r₁ = ofOrientation r₂ ↔ r₁ = r₂ := by
  decide

/-- Applies a clockwise rotation to a Rubik's cube. -/
def rotate (cube : PRubik) (r : Orientation) : PRubik :=
  cube * ofOrientation r

@[simp]
theorem rotate_inj_left {cube₁ cube₂ : PRubik} {r : Orientation} :
    cube₁.rotate r = cube₂.rotate r ↔ cube₁ = cube₂ :=
  mul_left_inj _

@[simp]
theorem rotate_inj_right {cube : PRubik} {r₁ r₂ : Orientation} :
    cube.rotate r₁ = cube.rotate r₂ ↔ r₁ = r₂ := by
  rw [rotate, rotate, mul_right_inj, ofOrientation_inj]

@[simp]
theorem rotate₄ (cube : PRubik) (r : Orientation) :
    (((cube.rotate r).rotate r).rotate r).rotate r = cube := by
  simp_rw [rotate, mul_assoc]
  convert mul_one _
  ext e
  · exact congr_fun (rotate_edgePiece₄ r) e
  · exact congr_fun (rotate_cornerPiece₄ r) e

@[simp]
theorem parity_ofOrientation : ∀ r, parity (ofOrientation r) = 1 := by
  decide

@[simp]
theorem edgeFlip_ofOrientation : ∀ r, edgeFlip (ofOrientation r) = 1 := by
  decide

@[simp]
theorem cornerRotation_ofOrientation : ∀ r, cornerRotation (ofOrientation r) = 1 := by
  decide

/-- A single rotation is always a valid move. -/
theorem isValid_ofOrientation (r : Orientation) : IsValid (ofOrientation r) :=
  isValid_iff.2 ⟨parity_ofOrientation r, edgeFlip_ofOrientation r, cornerRotation_ofOrientation r⟩

end PRubik

abbrev Moves : Type := List Orientation

namespace Moves

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

/-- Performs a sequence of moves in inverse order. -/
def symm : Moves → Moves
  | [] => ∅
  | (a :: l) => symm l ++ [a, a, a]

@[simp]
theorem symm_nil : symm [] = [] :=
  rfl

@[simp]
theorem symm_cons (r : Orientation) (m : Moves) : symm (r :: m) = symm m ++ [r, r, r] :=
  rfl

@[simp]
theorem symm_append (l m : Moves) : symm (l ++ m) = symm m ++ symm l := by
  induction l with
  | nil => simp
  | cons r m IH => simp [IH]

end Moves

namespace PRubik

/-- Applies a sequence of moves to a Rubik's cube. -/
def move (cube : PRubik) (m : Moves) : PRubik :=
  m.foldl PRubik.rotate cube

@[simp]
theorem move_nil (cube : PRubik) : cube.move [] = cube :=
  rfl

@[simp]
theorem move_cons (cube : PRubik) (r : Orientation) (m : Moves) :
    cube.move (r :: m) = (cube.rotate r).move m :=
  List.foldl_cons _ _

@[simp]
theorem move_append (cube : PRubik) (l m : Moves) : cube.move (l ++ m) = (cube.move l).move m :=
  List.foldl_append _ _ _ _

@[simp]
theorem mul_move (cube₁ cube₂ : PRubik) (m : Moves) :
    (cube₁ * cube₂).move m = cube₁ * (cube₂.move m) := by
  revert cube₂
  induction m with
  | nil => exact fun _ ↦ rfl
  | cons r m IH =>
      intro cube₂
      rw [move_cons, move_cons, rotate, rotate, mul_assoc, IH]

@[simp]
theorem move_symm_move (cube : PRubik) (m : Moves) : (cube.move m.symm).move m = cube := by
  revert cube
  induction m with
  | nil => simp
  | cons r m IH =>
      intro cube
      simp [IH]

@[simp]
theorem move_move_symm (cube : PRubik) (m : Moves) : (cube.move m).move m.symm = cube := by
  revert cube
  induction m with
  | nil => simp
  | cons r m IH =>
      intro cube
      simp
      rw [← rotate_inj_left, rotate₄, IH]

@[simp]
theorem move_inj {cube₁ cube₂ : PRubik} (m : Moves) :
    cube₁.move m = cube₂.move m ↔ cube₁ = cube₂ := by
  constructor
  · intro h
    simpa using congr_arg (fun cube ↦ cube.move m.symm) h
  · rintro rfl
    rfl

@[simp]
theorem move_symm_symm {cube : PRubik} {m : Moves} : cube.move m.symm.symm = cube.move m := by
  rw [← move_inj m.symm, move_symm_move, move_move_symm]

@[simp]
theorem move_one_inv : (move 1 m)⁻¹ = move 1 m.symm := by
  rw [inv_eq_iff_mul_eq_one, ← mul_move, mul_one, move_move_symm]

/-- A Rubik's cube is solvable when there exists a sequence of moves that brings it to the solved
state. -/
def IsSolvable (cube : PRubik) : Prop :=
  ∃ m : Moves, cube.move m = 1

theorem isSolvable_one : IsSolvable 1 :=
  ⟨[], rfl⟩

theorem IsSolvable.mul (h₁ : IsSolvable cube₁) (h₂ : IsSolvable cube₂) :
    IsSolvable (cube₁ * cube₂) := by
  obtain ⟨l, hl⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  use m ++ l
  rwa [move_append, mul_move, hm, mul_one]

theorem IsSolvable.symm (h : IsSolvable cube) : IsSolvable cube⁻¹ := by
  obtain ⟨m, hm⟩ := h
  use m.symm
  rw [← move_inj m.symm, move_move_symm] at hm
  rw [hm, move_one_inv, move_symm_symm, move_move_symm]

theorem isSolvable_symm_iff : IsSolvable cube⁻¹ ↔ IsSolvable cube := by
  refine ⟨?_, IsSolvable.symm⟩
  intro h
  rw [← inv_inv cube]
  exact h.symm

theorem IsSolvable.move (h : IsSolvable cube) (m : Moves) : IsSolvable (cube.move m) := by
  obtain ⟨l, hl⟩ := h
  use m.symm ++ l
  simp [hl]

/-- A cube is solvable if it can be scrambled from a solved state. -/
theorem isSolvable_iff : IsSolvable cube ↔ ∃ m : Moves, cube = move 1 m := by
  constructor <;>
  rintro ⟨m, hm⟩ <;>
  use m.symm
  · rw [← move_inj m, hm, move_symm_move]
  · rw [hm, move_move_symm]

theorem IsValid.move (h : IsValid cube) (m : Moves) : IsValid (cube.move m) := by
  revert cube
  induction m with
  | nil => exact id
  | cons r m IH =>
      intro cube h
      rw [move_cons, rotate, mul_move]
      exact h.mul (IH (isValid_ofOrientation r))

/-- A solvable cube is valid. -/
theorem IsSolvable.isValid (h : IsSolvable cube) : IsValid cube := by
  obtain ⟨m, hm⟩ := isSolvable_iff.1 h
  rw [hm]
  exact isValid_one.move m

end PRubik

open Orientation
#eval PRubik.move 1 [U, R, R, F, B, R, B, B, R, U, U, L, B, B, R, U, U, U, D, D, D, R, R, F, R, R,
  R, L, B, B, U, U, F, F]
