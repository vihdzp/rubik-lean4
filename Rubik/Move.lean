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
theorem ofOrientation₄ (r : Orientation) : (ofOrientation r) ^ 4 = 1 := by
  simp_rw [ofOrientation, pow_succ, mul_assoc]
  convert mul_one _
  ext e
  · exact congr_fun (rotate_edgePiece₄ r) e
  · exact congr_fun (rotate_cornerPiece₄ r) e

theorem ofOrientation_inv (r : Orientation) : (ofOrientation r)⁻¹ = (ofOrientation r) ^ 3 := by
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

@[simp]
theorem symm_replicate (n : ℕ) (a : Orientation) : symm (replicate n a) = replicate (3 * n) a := by
  induction n with
  | zero => rfl
  | succ n IH =>
      rw [replicate_succ, symm_cons, IH, mul_add, replicate_add]
      rfl

/-- Removes any instances of four consecutive rotations from a list of moves.

Note that this might still contain four consecutive rotations, e.g.
`deduplicateCore [L, L, F, F, F, F, L, L] = [L, L, L, L]`. -/
def deduplicateCore : Moves → Moves
  | [] => []
  | [a] => [a]
  | [a, b] => [a, b]
  | [a, b, c] => [a, b, c]
  | a :: b :: c :: d :: m =>
      if a ≠ b then a :: deduplicateCore (b :: c :: d :: m) else
      if b ≠ c then a :: b :: deduplicateCore (c :: d :: m) else
      if c ≠ d then a :: b :: c :: deduplicateCore (d :: m) else deduplicateCore m

@[simp]
theorem deduplicateCore_nil : deduplicateCore [] = [] :=
  rfl

theorem deduplicateCore_cons (h : a ≠ b) (m : Moves) :
    deduplicateCore (a :: b :: m) = a :: deduplicateCore (b :: m) :=
  match m with
  | [] => rfl
  | [c] => rfl
  | c :: d :: m => by rw [deduplicateCore, if_pos h]

theorem deduplicateCore_cons₂ (h : a ≠ b) (m : Moves) :
    deduplicateCore (a :: a :: b :: m) = a :: a :: deduplicateCore (b :: m) :=
  match m with
  | [] => rfl
  | c :: m => by rw [deduplicateCore, if_neg (not_not.2 rfl), if_pos h]

theorem deduplicateCore_cons₃ (h : a ≠ b) (m : Moves) :
    deduplicateCore (a :: a :: a :: b :: m) = a :: a :: a :: deduplicateCore (b :: m) := by
  rw [deduplicateCore, if_neg (not_not.2 rfl), if_neg (not_not.2 rfl), if_pos h]

@[simp]
theorem deduplicateCore_cons₄ (a : Orientation) (m : Moves) :
    deduplicateCore (a :: a :: a :: a :: m) = deduplicateCore m := by
  rw [deduplicateCore]
  simp_rw [if_neg (not_not.2 rfl)]

theorem replicate_cases (m : Moves) : (∃ a n, m = replicate n a) ∨
    ∃ (a b : Orientation) (n : ℕ+) (l : Moves), a ≠ b ∧ m = replicate n a ++ (b :: l) := by
  cases m with
  | nil => exact Or.inl ⟨default, 0, rfl⟩
  | cons a m =>
      obtain ⟨b, n, rfl⟩ | ⟨b, c, n, l, h, rfl⟩ := replicate_cases m <;>
      obtain rfl | h' := eq_or_ne a b
      · exact Or.inl ⟨a, n + 1, rfl⟩
      · cases n with
        | zero => exact Or.inl ⟨a, 1, rfl⟩
        | succ n => exact Or.inr ⟨a, b, 1, replicate n b, h', rfl⟩
      · exact Or.inr ⟨a, c, n + 1, l, h, rfl⟩
      · refine Or.inr ⟨a, b, 1, (replicate n.natPred b ++ c :: l), h', ?_⟩
        simp [← cons_append]
        rw [← PNat.natPred_add_one]
        rfl

theorem replicateRecOn {p : Moves → Prop} (m : Moves) (hr : ∀ a n, p (replicate n a))
    (hi : ∀ a b n l, a ≠ b → p (b :: l) → p (replicate n a ++ b :: l)) : p m := by
  obtain ⟨a, n, rfl⟩ | ⟨a, b, n, l, h, rfl⟩ := replicate_cases m
  · exact hr a n
  · exact hi a b n _ h (replicateRecOn _ hr hi)
termination_by m.length

@[simp]
theorem deduplicateCore_replicate (n : ℕ) : deduplicateCore (replicate n a) = replicate (n % 4) a :=
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | n + 4 => by
      rw [add_comm, replicate_add, Nat.add_mod_left]
      change deduplicateCore (a :: a :: a :: a :: (replicate n a)) = _
      rw [deduplicateCore_cons₄, deduplicateCore_replicate]

theorem deduplicateCore_replicate_append (h : a ≠ b) (n : ℕ) (m : Moves) :
    deduplicateCore (replicate n a ++ b :: m) =
    replicate (n % 4) a ++ deduplicateCore (b :: m) :=
  match n with
  | 0 => rfl
  | 1 => by simp [deduplicateCore_cons h]
  | 2 => by simp [deduplicateCore_cons₂ h]
  | 3 => by simp [deduplicateCore_cons₃ h]
  | n + 4 => by
      rw [add_comm, replicate_add, Nat.add_mod_left]
      change deduplicateCore (a :: a :: a :: a :: (replicate n a ++ b :: m)) = _
      rw [deduplicateCore_cons₄, deduplicateCore_replicate_append h]

@[simp]
theorem deduplicateCore_symm_symm (m : Moves) :
    deduplicateCore m.symm.symm = deduplicateCore m := by
  apply replicateRecOn m
  · simp [← mul_assoc, Nat.mul_mod]
  · intro a b n l h
    simp [deduplicateCore_replicate_append h, ← mul_assoc, Nat.mul_mod]

theorem deduplicateCore_eq_or_length_lt (m : Moves) :
    deduplicateCore m = m ∨ (deduplicateCore m).length < m.length :=
  match m with
  | [] => Or.inl rfl
  | [a] => Or.inl rfl
  | [a, b] => Or.inl rfl
  | [a, b, c] => Or.inl rfl
  | a :: b :: c :: d :: m => by
      rw [deduplicateCore]
      split_ifs with h₁ h₂ h₃
      · obtain h | h := deduplicateCore_eq_or_length_lt (b :: c :: d :: m)
        · rw [h]
          exact Or.inl rfl
        · simp_rw [length_cons, add_lt_add_iff_right]
          exact Or.inr h
      · obtain h | h := deduplicateCore_eq_or_length_lt (c :: d :: m)
        · rw [h]
          exact Or.inl rfl
        · simp_rw [length_cons, add_lt_add_iff_right]
          exact Or.inr h
      · obtain h | h := deduplicateCore_eq_or_length_lt (d :: m)
        · rw [h]
          exact Or.inl rfl
        · simp_rw [length_cons, add_lt_add_iff_right]
          exact Or.inr h
      · rw [not_not] at h₁ h₂ h₃
        subst h₁ h₂ h₃
        right
        obtain h | h := deduplicateCore_eq_or_length_lt m
        · rw [h]
          simp_rw [length_cons, add_assoc]
          exact lt_add_of_pos_right _ (Nat.zero_lt_succ 3)
        · apply h.trans_le
          simp [add_assoc]

theorem deduplicateCore_length_le (m : Moves) : (deduplicateCore m).length ≤ m.length := by
  obtain h | h := deduplicateCore_eq_or_length_lt m
  · rw [h]
  · exact h.le

/-- Recursively removes any instances of four consecutive rotations from a list of moves. -/
def deduplicate (m : Moves) : Moves :=
  let l := deduplicateCore m
  if h : l = m then m else
    have := (deduplicateCore_eq_or_length_lt m).resolve_left h
    deduplicate l
termination_by m.length

theorem deduplicate_of_eq (h : deduplicateCore m = m) : deduplicate m = m := by
  rw [deduplicate]
  exact if_pos h

theorem deduplicate_of_ne (h : deduplicateCore m ≠ m) :
    deduplicate m = deduplicate (deduplicateCore m) := by
  rw [deduplicate]
  exact if_neg h

@[simp]
theorem deduplicate_nil : deduplicate [] = [] :=
  deduplicate_of_eq rfl

theorem deduplicate_eq_iterate (m : Moves) : ∃ n, deduplicate m = deduplicateCore^[n] m := by
  obtain h | h := eq_or_ne (deduplicateCore m) m
  · use 1
    rw [deduplicate_of_eq h, Function.iterate_one, h]
  · have := (deduplicateCore_eq_or_length_lt m).resolve_left h
    obtain ⟨n, hn⟩ := deduplicate_eq_iterate (deduplicateCore m)
    use n + 1
    rw [deduplicate_of_ne h, Function.iterate_succ_apply, hn]
termination_by m.length

@[simp]
theorem deduplicate_deduplicateCore (m : Moves) :
    deduplicate (deduplicateCore m) = deduplicate m := by
  obtain h | h := eq_or_ne (deduplicateCore m) m
  · rw [h]
  · rw [deduplicate_of_ne h]

@[simp]
theorem deduplicateCore_deduplicate (m : Moves) :
    deduplicateCore (deduplicate m) = deduplicate m := by
  rw [deduplicate]
  split_ifs with h
  · exact h
  · have := (deduplicateCore_eq_or_length_lt m).resolve_left h
    exact deduplicateCore_deduplicate _
termination_by m.length

@[simp]
theorem deduplicate_deduplicate (m : Moves) : deduplicate (deduplicate m) = deduplicate m :=
  deduplicate_of_eq (deduplicateCore_deduplicate m)

@[simp]
theorem deduplicate_cons₄ (a : Orientation) (m : Moves) :
    deduplicate (a :: a :: a :: a :: m) = deduplicate m := by
  rw [← deduplicate_deduplicateCore, deduplicateCore_cons₄, deduplicate_deduplicateCore]

@[simp]
theorem deduplicate_symm_symm (m : Moves) : deduplicate m.symm.symm = deduplicate m := by
  rw [← deduplicate_deduplicateCore, deduplicateCore_symm_symm, deduplicate_deduplicateCore]

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

/-- A Rubik's cube is solvable when there exists a sequence of moves that can assemble it from the
solved state.

See `isSolvable_iff` for the equivalence with being able to unscramble the cube. -/
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

theorem IsSolvable.symm (h : IsSolvable cube) : IsSolvable cube⁻¹ := by
  obtain ⟨m, hm⟩ := h
  use m.symm
  rwa [move_symm, inv_inj]

theorem isSolvable_symm_iff : IsSolvable cube⁻¹ ↔ IsSolvable cube := by
  refine ⟨?_, IsSolvable.symm⟩
  intro h
  rw [← inv_inv cube]
  exact h.symm

/-- A cube is solvable iff it can be unscrambled. -/
theorem isSolvable_iff : IsSolvable cube ↔ ∃ m, cube * move m = 1 := by
  constructor <;>
  rintro ⟨m, h⟩
  · use m.symm
    rw [move_symm, h, mul_inv_cancel]
  · rw [← inv_eq_iff_mul_eq_one, inv_eq_iff_eq_inv] at h
    exact h ▸ (isSolvable_move m).symm

theorem isValid_move (m : Moves) : IsValid (move m) := by
  induction m with
  | nil => exact isValid_one
  | cons r m IH =>
      rw [move_cons]
      exact (isValid_ofOrientation r).mul IH

/-- A solvable cube is valid. -/
theorem IsSolvable.isValid (h : IsSolvable cube) : IsValid cube := by
  obtain ⟨m, rfl⟩ := h
  exact isValid_move m

end PRubik

namespace Rubik

/-- Applies a sequence of moves to a solved Rubik's cube. -/
def move (m : Moves) : Rubik :=
  ⟨_, PRubik.isValid_move m⟩

end Rubik
