import Rubik.PRubik

/-!
We define the Rubik's cube corresponding to any given orientation. We use this to define
`PRubik.move`, which applies any sequence of moves from the solved state.
-/

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
      rotate_edgePiece r, _,
      funext_iff.1 (rotate_edgePiece₄ r),
      funext_iff.1 (rotate_edgePiece₄ r)⟩
  cornerPieceEquiv := ⟨
      rotate_cornerPiece r, _,
      funext_iff.1 (rotate_cornerPiece₄ r),
      funext_iff.1 (rotate_cornerPiece₄ r)⟩
  edge_flip e := by
    dsimp
    simp_rw [rotate_edgePiece, EdgePiece.flip_toFinset]
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

@[simp]
theorem ofOrientation₄ (r : Orientation) : ofOrientation r ^ 4 = 1 := by
  simp_rw [ofOrientation, pow_succ, mul_assoc]
  convert mul_one _
  ext e
  · exact congr_fun (rotate_edgePiece₄ r) e
  · exact congr_fun (rotate_cornerPiece₄ r) e

theorem ofOrientation_inv (r : Orientation) : (ofOrientation r)⁻¹ = ofOrientation r ^ 3 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', ofOrientation₄]

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

/-- A list of moves to be performed on a Rubik's cube.

The `Repr` instance on this type will automatically deduplicate the list for convenience. This means
for instance that `[L, L, F, F, F, F, L, L]` will print as `[]`, despite being different lists. -/
abbrev Moves : Type := List Orientation

namespace Moves

open List

/-- Turn right face. -/
protected abbrev R : Moves := [Orientation.R]
/-- Turn up face. -/
protected abbrev U : Moves := [Orientation.U]
/-- Turn front face. -/
protected abbrev F : Moves := [Orientation.F]

/-- Turn left face. -/
protected abbrev L : Moves := [Orientation.L]
/-- Turn down face. -/
protected abbrev D : Moves := [Orientation.D]
/-- Turn back face. -/
protected abbrev B : Moves := [Orientation.B]

/-- Turn right face twice. -/
abbrev R2 : Moves := Moves.R ++ Moves.R
/-- Turn up face twice. -/
abbrev U2 : Moves := Moves.U ++ Moves.U
/-- Turn front face twice. -/
abbrev F2 : Moves := Moves.F ++ Moves.F

/-- Turn left face twice. -/
abbrev L2 : Moves := Moves.L ++ Moves.L
/-- Turn down face twice. -/
abbrev D2 : Moves := Moves.D ++ Moves.D
/-- Turn back face twice. -/
abbrev B2 : Moves := Moves.B ++ Moves.B

/-- Turn right face backwards. -/
abbrev R' : Moves := R2 ++ Moves.R
/-- Turn up face backwards. -/
abbrev U' : Moves := U2 ++ Moves.U
/-- Turn front face backwards. -/
abbrev F' : Moves := F2 ++ Moves.F

/-- Turn left face backwards. -/
abbrev L' : Moves := L2 ++ Moves.L
/-- Turn down face backwards. -/
abbrev D' : Moves := D2 ++ Moves.D
/-- Turn back face backwards. -/
abbrev B' : Moves := B2 ++ Moves.B

/-- Performs a sequence of moves backwards, turning each face in the opposite direction. -/
def symm : Moves → Moves
  | [] => []
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

@[simp]
theorem symm_replicate (n : ℕ) (a : Orientation) : symm (replicate n a) = replicate (3 * n) a := by
  induction n with
  | zero => rfl
  | succ n IH =>
    rw [replicate_succ, symm_cons, IH, mul_add, replicate_add]
    rfl

-- TODO: PR to Lean 4
theorem Option.or_some_right (a : Option α) (b : α) : a.or (some b) = a.getD b := by
  cases a <;> rfl

@[simp]
theorem head?_symm (m : Moves) : head? m.symm = getLast? m := by
  induction m with
  | nil => rfl
  | cons a m IH =>
    rw [symm_cons, head?_append, head?_cons, getLast?_cons, IH, Option.or_some_right]

@[simp]
theorem getLast?_symm (m : Moves) : getLast? m.symm = head? m := by
  cases m with
  | nil => rfl
  | cons a m =>
    rw [symm_cons, getLast?_append, getLast?_cons_cons, getLast?_cons_cons, getLast?_singleton,
      Option.or_some, head?_cons]



end Moves

namespace PRubik

/-- Applies a sequence of moves to a solved Rubik's cube. -/
def move (m : Moves) : PRubik :=
  m.foldl (fun r ↦ · * ofOrientation r) 1

@[simp]
theorem move_nil : move [] = 1 :=
  rfl

@[simp]
theorem foldl_eq_move (cube : PRubik) (m : Moves) :
    m.foldl (fun r ↦ · * ofOrientation r) cube = cube * move m := by
  revert cube
  induction m with
  | nil => exact fun _ ↦ rfl
  | cons a m IH =>
    intro cube
    simp_rw [move, List.foldl_cons, IH]
    rw [← mul_assoc]
    rfl

@[simp]
theorem move_cons (r : Orientation) (m : Moves) :
    move (r :: m) = (ofOrientation r) * move m := by
  rw [move, List.foldl_cons, foldl_eq_move]
  rfl

@[simp]
theorem move_append (l m : Moves) : move (l ++ m) = move l * move m := by
  rw [move, List.foldl_append, foldl_eq_move, foldl_eq_move, one_mul]

@[simp]
theorem move_symm (m : Moves) : move m.symm = (move m)⁻¹ := by
  induction m with
  | nil => simp
  | cons r m IH => simp [IH, ofOrientation_inv, pow_succ, mul_assoc]

theorem move_replicate (n : ℕ) (a : Orientation) :
    move (List.replicate n a) = move (List.replicate (n % 4) a) :=
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | n + 4 => by
    rw [List.replicate_add, move_append, Nat.add_mod_right, move_replicate, mul_right_eq_self]
    exact ofOrientation₄ a

/-- A Rubik's cube is solvable when there exists a sequence of moves that can assemble it from the
solved state. See `isSolvable_iff` for the equivalence with being able to unscramble the cube.

A main result we show is `isValid_iff_isSolvable`: a Rubik's cube can be solved iff it satisfies the
Rubik's cube invariant. -/
def IsSolvable (cube : PRubik) : Prop :=
  ∃ m : Moves, move m = cube

theorem isSolvable_one : IsSolvable 1 :=
  ⟨[], rfl⟩

theorem isSolvable_move (m : Moves) : IsSolvable (move m) :=
  ⟨m, rfl⟩

theorem IsSolvable.mul (h₁ : IsSolvable cube₁) (h₂ : IsSolvable cube₂) :
    IsSolvable (cube₁ * cube₂) := by
  obtain ⟨l, hl⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  use l ++ m
  rw [move_append, hl, hm]

theorem IsSolvable.inv (h : IsSolvable cube) : IsSolvable cube⁻¹ := by
  obtain ⟨m, hm⟩ := h
  use m.symm
  rwa [move_symm, inv_inj]

theorem isSolvable_inv_iff : IsSolvable cube⁻¹ ↔ IsSolvable cube :=
  ⟨IsSolvable.inv, IsSolvable.inv⟩

/-- A cube is solvable iff it can be unscrambled. -/
theorem isSolvable_iff : IsSolvable cube ↔ ∃ m, cube * move m = 1 := by
  constructor <;>
  rintro ⟨m, h⟩
  · use m.symm
    rw [move_symm, h, mul_inv_cancel]
  · rw [← inv_eq_iff_mul_eq_one, inv_eq_iff_eq_inv] at h
    exact h ▸ (isSolvable_move m).inv

theorem isValid_move (m : Moves) : IsValid (move m) := by
  induction m with
  | nil => exact isValid_one
  | cons r m IH =>
      rw [move_cons]
      exact (isValid_ofOrientation r).mul IH

/-- A solvable cube is valid, i.e. retains the invariant. -/
theorem IsSolvable.isValid (h : IsSolvable cube) : IsValid cube := by
  obtain ⟨m, rfl⟩ := h
  exact isValid_move m

end PRubik

namespace Rubik

/-- Applies a sequence of moves to a solved Rubik's cube. -/
def move (m : Moves) : Rubik :=
  ⟨_, PRubik.isValid_move m⟩

@[simp]
theorem val_move (m : Moves) : (move m).val = PRubik.move m :=
  rfl

@[simp]
theorem move_nil : move [] = 1 :=
  rfl

@[simp]
theorem move_append (l m : Moves) : move (l ++ m) = move l * move m :=
  Subtype.ext <| PRubik.move_append l m

end Rubik
