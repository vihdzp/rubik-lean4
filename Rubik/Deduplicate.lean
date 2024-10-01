import Rubik.Move
import Rubik.RunLength

/-!
We define `Moves.deduplicate`, which can be used to remove "obvious redundancies" within a sequence
of moves, in the form of a single face being turned four or more consecutive times.
-/

open List

namespace Moves

/-- Removes any instances of four consecutive rotations from a list of moves.

Note that this might still contain four consecutive rotations, e.g.
`deduplicateCore [L, L, F, F, F, F, L, L] = [L, L, L, L]`. -/
def deduplicateCore (m : Moves) : Moves :=
  runLengthRecOn m [] fun n a _ _ IH ↦ replicate (n % 4) a ++ IH

@[simp]
theorem deduplicateCore_nil : deduplicateCore [] = [] :=
  rfl

theorem deduplicateCore_append (n : ℕ) {a : Orientation} {m : Moves} (ha : a ∉ m.head?) :
    deduplicateCore (replicate n a ++ m) = replicate (n % 4) a ++ deduplicateCore m := by
  obtain rfl | hn := n.eq_zero_or_pos
  · rfl
  · exact runLengthRecOn_append hn ha _ _

@[simp]
theorem deduplicateCore_replicate (n : ℕ) (a : Orientation) :
    deduplicateCore (replicate n a) = replicate (n % 4) a := by
  convert deduplicateCore_append n (m := []) (Option.not_mem_none a) <;> simp

@[simp]
theorem deduplicateCore_symm_symm (m : Moves) :
    deduplicateCore m.symm.symm = deduplicateCore m := by
  apply runLengthRecOn m
  · rfl
  · intro n a l ha IH
    have : 3 * 3 % 4 = 1 := rfl
    rw [symm_append, symm_append, deduplicateCore_append n ha, symm_replicate, symm_replicate,
      deduplicateCore_append, IH, append_cancel_right_eq, ← mul_assoc, ← Nat.mod_mul_mod,
      this, one_mul]
    rwa [head?_symm, getLast?_symm]

theorem deduplicateCore_eq_or_length_lt (m : Moves) :
    deduplicateCore m = m ∨ (deduplicateCore m).length < m.length := by
  apply runLengthRecOn m
  · exact Or.inl rfl
  · intro n a l ha IH
    rw [deduplicateCore_append n ha, length_append, length_append,
      length_replicate, length_replicate]
    obtain hn | hn := (Nat.mod_le n 4).lt_or_eq
    · apply Or.inr (add_lt_add_of_lt_of_le hn _)
      obtain hl | hl := IH
      · rw [hl]
      · exact hl.le
    · rwa [hn, append_cancel_left_eq, add_lt_add_iff_left]

theorem deduplicateCore_length_le (m : Moves) : (deduplicateCore m).length ≤ m.length := by
  obtain h | h := deduplicateCore_eq_or_length_lt m
  · rw [h]
  · exact h.le

/-- Recursively removes any instances of four consecutive rotations from a list of moves. -/
def deduplicate (m : Moves) : Moves :=
  let l := deduplicateCore m
  if l = m then m else deduplicate l
termination_by m.length
decreasing_by apply (deduplicateCore_eq_or_length_lt m).resolve_left; assumption

theorem deduplicate_of_eq (h : deduplicateCore m = m) : deduplicate m = m := by
  rw [deduplicate, if_pos h]

@[simp]
theorem deduplicate_nil : deduplicate [] = [] :=
  deduplicate_of_eq rfl

@[simp]
theorem deduplicate_deduplicateCore (m : Moves) :
    deduplicate (deduplicateCore m) = deduplicate m := by
  obtain h | h := eq_or_ne (deduplicateCore m) m
  · rw [h]
  · conv_rhs => rw [deduplicate, if_neg h]

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

theorem deduplicate_eq_iterate (m : Moves) : ∃ n, deduplicate m = deduplicateCore^[n] m := by
  obtain h | h := eq_or_ne (deduplicateCore m) m
  · use 1
    rw [deduplicate_of_eq h, Function.iterate_one, h]
  · have := (deduplicateCore_eq_or_length_lt m).resolve_left h
    obtain ⟨n, hn⟩ := deduplicate_eq_iterate (deduplicateCore m)
    use n + 1
    rw [← deduplicate_deduplicateCore, Function.iterate_succ_apply, hn]
termination_by m.length

@[simp]
theorem deduplicate_replicate (n : ℕ) : deduplicate (replicate n a) = replicate (n % 4) a := by
  rw [← deduplicate_deduplicateCore, deduplicateCore_replicate, deduplicate_of_eq]
  rw [deduplicateCore_replicate, Nat.mod_mod]

@[simp]
theorem deduplicate_symm_symm (m : Moves) : deduplicate m.symm.symm = deduplicate m := by
  rw [← deduplicate_deduplicateCore, deduplicateCore_symm_symm, deduplicate_deduplicateCore]

theorem deduplicate_length_le (m : Moves) : (deduplicate m).length ≤ m.length := by
  obtain ⟨n, hn⟩ := deduplicate_eq_iterate m
  rw [hn]
  clear hn
  induction n generalizing m with
  | zero => rw [Function.iterate_zero_apply]
  | succ n IH =>
    rw [Function.iterate_succ_apply']
    exact (deduplicateCore_length_le _).trans (IH _)

theorem deduplicate_eq_or_length_lt (m : Moves) :
    deduplicate m = m ∨ (deduplicate m).length < m.length := by
  obtain hm | hm := deduplicateCore_eq_or_length_lt m
  · exact Or.inl (deduplicate_of_eq hm)
  · rw [← deduplicate_deduplicateCore]
    exact Or.inr ((deduplicate_length_le _).trans_lt hm)

/-- Whether a sequence of moves has been deduplicated. -/
def IsDeduplicated (m : Moves) : Prop :=
  deduplicateCore m = m

instance : DecidablePred IsDeduplicated :=
  inferInstanceAs (DecidablePred (_ = ·))

theorem isDeduplicated_nil : IsDeduplicated [] :=
  rfl

theorem isDeduplicated_deduplicate (m : Moves) : IsDeduplicated (deduplicate m) :=
  deduplicateCore_deduplicate m

theorem isDeduplicated_iff_deduplicateCore {m : Moves} : IsDeduplicated m ↔ deduplicateCore m = m :=
  Iff.rfl

alias ⟨IsDeduplicated.deduplicateCore_eq, _⟩ := isDeduplicated_iff_deduplicateCore

theorem isDeduplicated_iff_deduplicate {m : Moves} : IsDeduplicated m ↔ deduplicate m = m := by
  refine ⟨deduplicate_of_eq, fun h ↦ ?_⟩
  obtain hm | hm := deduplicateCore_eq_or_length_lt m
  · exact hm
  · have := (deduplicate_length_le _).trans_lt hm
    rw [deduplicate_deduplicateCore, h] at this
    cases this.false

alias ⟨IsDeduplicated.deduplicate_eq, _⟩ := isDeduplicated_iff_deduplicate

theorem isDeduplicated_of_append_left {l m : Moves} (h : IsDeduplicated (l ++ m)) :
    IsDeduplicated l := by
  sorry

theorem isDeduplicated_of_append_right {l m : Moves} (h : IsDeduplicated (l ++ m)) :
    IsDeduplicated m := by
  sorry

theorem isDeduplicated_replicate_iff {n : ℕ} {a : Orientation} :
    IsDeduplicated (replicate n a) ↔ n ≤ 3 := by
  rw [IsDeduplicated, deduplicateCore_replicate, replicate_left_inj]
  omega

theorem isDeduplicated_append {n : ℕ} (hn : n ≤ 3) {a : Orientation}
    {m : Moves} (hm : IsDeduplicated m) (ha : a ∉ m.head?) :
    IsDeduplicated (replicate n a ++ m) := by
  rw [IsDeduplicated, deduplicateCore_append n ha, hm.deduplicateCore_eq,
    append_cancel_right_eq, replicate_inj, Nat.mod_succ_eq_iff_lt, Nat.lt_succ]
  exact ⟨hn, Or.inr rfl⟩ 

/-- Recursion on deduplicated sequences of moves. -/
def isDeduplicatedRecOn {m : Moves} (hm : IsDeduplicated m) {p : Moves → Sort*} (hn : p [])
    (hi : ∀ {n : ℕ+} (_ : n ≤ 3) {a m}, IsDeduplicated m → a ∉ m.head? →
      p m → p (replicate n a ++ m)) : p m :=
  runLengthRecOn m (fun _ ↦ hn) (fun _ _ m ha (IH : _ → _) hm ↦
    have hm' : IsDeduplicated m := isDeduplicated_of_append_right hm
    hi (isDeduplicated_replicate_iff.1 (isDeduplicated_of_append_left hm)) hm' ha (IH hm')) hm

@[simp]
theorem isDeduplicatedRecOn_nil {p : Moves → Sort*} (hn : p [])
    (hi : ∀ {n : ℕ+} (_ : n ≤ 3) {a m}, IsDeduplicated m → a ∉ m.head? →
      p m → p (replicate n a ++ m)) : isDeduplicatedRecOn isDeduplicated_nil hn hi = hn :=
  rfl

theorem isDeduplicatedRecOn_append {p : Moves → Sort*} {n : ℕ} (h₁ : 0 < n) (h₂ : n ≤ 3)
    {a : Orientation} {m : Moves} (hm₁ : IsDeduplicated m) (hm₂ : a ∉ m.head?) (hn : p [])
    (hi : ∀ {n : ℕ+} (_ : n ≤ 3) {a m}, IsDeduplicated m → a ∉ m.head? →
      p m → p (replicate n a ++ m)) :
    isDeduplicatedRecOn (isDeduplicated_append h₂ hm₁ hm₂) hn hi =
      hi (n := ⟨n, h₁⟩) h₂ hm₁ hm₂ (isDeduplicatedRecOn hm₁ hn hi) := by
  rw [isDeduplicatedRecOn, runLengthRecOn_append h₁ hm₂]
  rfl

/-- Prints a (deduplicated) sequence of moves using Rubik's cube notation. -/
private def toString (m : Moves) : Option Lean.Format :=
  isDeduplicatedRecOn (isDeduplicated_deduplicate m) none
    @fun n _ a _ _ _ (IH : Option Lean.Format) ↦
    let n := match n with
      | 1 => ""
      | 2 => "2"
      | 3 => "'"
    let IH := match IH with
      | none => Std.Format.text ""
      | some x => " " ++ x
    some (repr a ++ n ++ IH)

instance : Repr Moves :=
  ⟨fun m _ ↦ (toString m).getD "[]"⟩

end Moves

namespace PRubik

@[simp]
theorem move_deduplicateCore (m : Moves) : move m.deduplicateCore = move m := by
  apply List.runLengthRecOn m
  · rfl
  · intro n a l ha IH
    rw [Moves.deduplicateCore_append n ha, move_append, move_append, IH]
    conv_rhs => rw [move_replicate]

@[simp]
theorem move_deduplicate (m : Moves) : move m.deduplicate = move m := by
  obtain ⟨n, hn⟩ := Moves.deduplicate_eq_iterate m
  rw [hn]
  clear hn
  induction n with
  | zero => rfl
  | succ n IH => rw [Function.iterate_succ_apply', move_deduplicateCore, IH]

end PRubik
