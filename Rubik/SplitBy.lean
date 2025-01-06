/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Data.List.SplitBy

/-!
# Split a list by a relation

This file expands upon the `List.splitBy` API.
-/

-- https://github.com/leanprover-community/mathlib4/pull/16837

namespace List

variable {α : Type*} {m : List α}

theorem head_flatten_of_head_ne_nil {l : List (List α)} (hl : l ≠ []) (hl' : l.head hl ≠ []) :
    l.flatten.head (flatten_ne_nil_iff.2 ⟨_, head_mem hl, hl'⟩) = (l.head hl).head hl' := by
  cases l with
  | nil => contradiction
  | cons a l =>
    simp_rw [flatten_cons, head_cons]
    exact head_append_of_ne_nil _

private theorem splitByLoop_eq_append {r : α → α → Bool} {l : List α} {a : α} {g : List α}
    (gs : List (List α)) : splitBy.loop r l a g gs = gs.reverse ++ splitBy.loop r l a g [] := by
  induction l generalizing a g gs with
  | nil => simp [splitBy.loop]
  | cons b l IH =>
    simp_rw [splitBy.loop]
    split <;> rw [IH]
    conv_rhs => rw [IH]
    simp

@[simp]
theorem splitBy_singleton (r : α → α → Bool) (a : α) : splitBy r [a] = [[a]] :=
  rfl

@[simp]
theorem splitBy_eq_nil {r : α → α → Bool} {l : List α} : l.splitBy r = [] ↔ l = [] := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have := flatten_splitBy r l
    rwa [h, flatten_nil, eq_comm] at this
  · rintro rfl
    rfl

private theorem splitByLoop_append {r : α → α → Bool} {l g : List α} {a : α}
    (h : (g.reverse ++ a :: l).Chain' fun x y ↦ r x y)
    (ha : ∀ h : m ≠ [], r ((a :: l).getLast (cons_ne_nil a l)) (m.head h) = false) :
    splitBy.loop r (l ++ m) a g [] = (g.reverse ++ a :: l) :: m.splitBy r := by
  induction l generalizing a g with
  | nil =>
    rw [nil_append]
    cases m with
    | nil => simp [splitBy.loop]
    | cons c m  =>
      rw [splitBy.loop]
      have := ha (cons_ne_nil c m)
      rw [getLast_singleton, head_cons] at this
      rw [this, splitByLoop_eq_append [_], splitBy]
      simp
  | cons b l IH =>
    rw [cons_append, splitBy.loop]
    split
    · rw [IH]
      · simp
      · simp [h]
      · rwa [getLast_cons (cons_ne_nil b l)] at ha
    · rw [chain'_append_cons_cons, ← Bool.ne_false_iff] at h
      have := h.2.1
      contradiction

set_option linter.docPrime false in
theorem splitBy_of_chain' {r : α → α → Bool} {l : List α} (hn : l ≠ [])
    (h : l.Chain' fun x y ↦ r x y) : splitBy r l = [l] := by
  cases l with
  | nil => contradiction
  | cons a l => rw [splitBy, ← append_nil l, splitByLoop_append] <;> simp [h]

theorem splitBy_append {r : α → α → Bool} {l : List α} (hn : l ≠ [])
    (h : l.Chain' fun x y ↦ r x y) (ha : ∀ h : m ≠ [], r (l.getLast hn) (m.head h) = false) :
    (l ++ m).splitBy r = l :: m.splitBy r := by
 cases l with
  | nil => contradiction
  | cons a l => rw [cons_append, splitBy, splitByLoop_append] <;> simp [h, ha]

theorem splitBy_append_cons {r : α → α → Bool} {l : List α} (hn : l ≠ []) {a : α} (m : List α)
    (h : l.Chain' fun x y ↦ r x y) (ha : r (l.getLast hn) a = false) :
    (l ++ a :: m).splitBy r = l :: (a :: m).splitBy r := by
  apply splitBy_append hn h fun _ ↦ ?_
  rwa [head_cons]

theorem splitBy_flatten {r : α → α → Bool} {l : List (List α)} (hn : [] ∉ l)
    (hc : ∀ m ∈ l, m.Chain' fun x y ↦ r x y)
    (hc' : l.Chain' fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false) :
    l.flatten.splitBy r = l := by
  induction l with
  | nil => rfl
  | cons a l IH =>
    rw [mem_cons, not_or, eq_comm] at hn
    rw [flatten_cons, splitBy_append hn.1 (hc _ (mem_cons_self a l)), IH hn.2 _ hc'.tail]
    · intro m hm
      exact hc _ (mem_cons_of_mem a hm)
    · intro h
      rw [chain'_cons'] at hc'
      obtain ⟨x, hx, _⟩ := flatten_ne_nil_iff.1 h
      obtain ⟨_, _, H⟩ := hc'.1 (l.head (ne_nil_of_mem hx)) (head_mem_head? _)
      rwa [head_flatten_of_head_ne_nil]

/-- A characterization of `splitBy m r` as the unique list `l` such that:
* The lists of `l` join to `m`.
* It does not contain the empty list.
* Every list in `l` is `Chain'` of `r`.
* The last element of each list in `l` is not related by `r` to the head of the next.
-/
theorem splitBy_eq_iff {r : α → α → Bool} {l : List (List α)} :
    m.splitBy r = l ↔ m = l.flatten ∧ [] ∉ l ∧ (∀ m ∈ l, m.Chain' fun x y ↦ r x y) ∧
      l.Chain' fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false := by
  constructor
  · rintro rfl
    exact ⟨(flatten_splitBy r m).symm, nil_not_mem_splitBy r m, fun _ ↦ chain'_of_mem_splitBy,
      chain'_getLast_head_splitBy r m⟩
  · rintro ⟨rfl, hn, hc, hc'⟩
    exact splitBy_flatten hn hc hc'

end List
