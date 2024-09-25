import Mathlib.Data.List.Chain

-- https://github.com/leanprover-community/mathlib4/pull/17106

namespace List

theorem chain_replicate [IsRefl α r] (n : ℕ) (a : α) : Chain r a (replicate n a) :=
  match n with
  | 0 => Chain.nil
  | n + 1 => Chain.cons (refl a) (chain_replicate n a)

theorem chain_eq_iff_eq_replicate {a : α} {l : List α} :
    Chain (· = ·) a l ↔ l = replicate l.length a :=
  match l with
  | [] => by simp
  | b :: l => by
    rw [chain_cons]
    simp (config := {contextual := true}) [eq_comm, replicate_succ, chain_eq_iff_eq_replicate]

theorem chain'_replicate [IsRefl α r] (n : ℕ) (a : α) : Chain' r (replicate n a) :=
  match n with
  | 0 => chain'_nil
  | n + 1 => chain_replicate n a

theorem chain'_eq_iff_eq_replicate {l : List α} :
    Chain' (· = ·) l ↔ ∀ a ∈ l.head?, l = replicate l.length a :=
  match l with
  | [] => by simp
  | a :: l => by simp [Chain', chain_eq_iff_eq_replicate, replicate_succ]

end List
