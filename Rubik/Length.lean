import Rubik.Algorithm

namespace Moves

/-- Length of a sequence of moves in the half-turn metric.

In this metric, any consecutive sequence of moves in a single face is counted as a single move. -/
def halfLength (m : Moves) : ℕ :=
  m.RunLength.length

@[simp]
theorem halfLength_nil : halfLength [] = 0 :=
  rfl

@[simp]
theorem halfLength_eq_zero (m : Moves) : halfLength m = 0 ↔ m = [] := by
  rw [halfLength, List.length_eq_zero, List.runLength_eq_nil]

@[simp]
theorem halfLength_singleton (a : Orientation) : halfLength [a] = 1 := by
  simp [halfLength]

theorem halfLength_le (m : Moves) : m.halfLength ≤ m.length :=
  List.length_runLength_le m

theorem halfLength_append_le (m n : Moves) : halfLength (m ++ n) ≤ halfLength m + halfLength n :=
  List.length_runLength_append_le m n

/-- Enumerates all deduplicated sequences of moves with a given half-length. -/
instance instFintypeHalfLength : ∀ n, Fintype { m : Moves // m.deduplicate = m ∧ m.halfLength = n }
  | 0 => ⟨{⟨[], by simp⟩}, sorry⟩
  | n + 1 => ⟨∅, sorry⟩

/-- Length of a sequence of moves in the quarter-turn metric.

In this metric, a consecutive sequence of moves in a single face of odd length counts as one move,
while a sequence of even length counts as two moves.

If the sequence is deduplicated, then this simply counts the number of quarter turns performed. -/
def quarterLength (m : Moves) : ℕ :=
  (m.RunLength.map fun x ↦ if Even x.1.1 then 2 else 1).sum

end Moves

namespace Rubik

/-- The "norm" of a Rubik's cube under the half-turn metric is the least amount of moves required to
solve it under said metric.

This function is computable, but the implementation is hopelessly naive - it will test all
deduplicated sequences of moves of increasing half-length until it finds one that works. -/
def halfNorm (cube : Rubik) : ℕ :=
  Nat.find (p := fun n ↦
    ∃ m : { m : Moves // m.deduplicate = m ∧ m.halfLength = n }, move m.1 = cube) (by
    obtain ⟨m, hm⟩ := Rubik.isSolvable cube
    exact ⟨_, ⟨_, ⟨Moves.deduplicate_deduplicate _, rfl⟩⟩,
      Subtype.ext (hm ▸ PRubik.move_deduplicate _)⟩
  )

end Rubik
