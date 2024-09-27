import Mathlib.GroupTheory.Perm.Basic

/-!
We prove various auxiliary results about equivalences.
-/

attribute [aesop norm] Equiv.swap_apply_def

namespace Equiv

variable {α : Type*}

@[simp]
theorem symm_mul (e₁ e₂ : Perm α) : (e₁ * e₂).symm = e₂.symm * e₁.symm :=
  rfl

variable (e : Perm α) (a b c d x y z : α) [DecidableEq α]

@[simp]
theorem swap_conj : e * (swap a b) * e⁻¹ = swap (e a) (e b) := by
  aesop

@[simp]
theorem swap_conj' : e⁻¹ * (swap a b) * e = swap (e⁻¹ a) (e⁻¹ b) :=
  swap_conj e⁻¹ a b

@[simp]
theorem swap_conj₂ : e * (swap a b) * (swap c d) * e⁻¹ =
    swap (e a) (e b) * swap (e c) (e d) := by
  have := congr_arg₂ (· * ·) (swap_conj e a b) (swap_conj e c d)
  simpa [-swap_conj, ← mul_assoc] using this

@[simp]
theorem swap_conj₂' : e⁻¹ * (swap a b) * (swap c d) * e =
    swap (e⁻¹ a) (e⁻¹ b) * swap (e⁻¹ c) (e⁻¹ d) :=
  swap_conj₂ e⁻¹ a b c d

/-- A cyclic permutation `a → b → c → a`. -/
@[aesop norm]
def cycle : Perm α :=
  if a = b ∨ b = c ∨ c = a then 1 else swap a b * swap b c

theorem cycle_fst {a b c : α} (h₂ : b ≠ c) (h₃ : c ≠ a) : cycle a b c a = b := by
  aesop

theorem cycle_snd {a b c : α} (h₁ : a ≠ b) (h₃ : c ≠ a) : cycle a b c b = c := by
  aesop

theorem cycle_thd {a b c : α} (h₁ : a ≠ b) (h₂ : b ≠ c) : cycle a b c c = a := by
  aesop

theorem cycle_apply_of_ne {a b c d : α} (h₁ : d ≠ a) (h₂ : d ≠ b) (h₃ : d ≠ c) :
    cycle a b c d = d := by
  aesop

theorem cycle_cyclic : cycle a b c = cycle b c a := by
  aesop

theorem cycle_inv : (cycle a b c)⁻¹ = cycle a c b := by
  aesop

@[simp]
theorem cycle_conj : e * (cycle a b c) * e⁻¹ = cycle (e a) (e b) (e c) := by
  aesop

@[simp]
theorem cycle_conj' : e⁻¹ * (cycle a b c) * e = cycle (e⁻¹ a) (e⁻¹ b) (e⁻¹ c) :=
  cycle_conj e⁻¹ a b c

@[simp]
theorem cycle_conj₂ : e * (cycle a b c) * (cycle x y z) * e⁻¹ =
    cycle (e a) (e b) (e c) * cycle (e x) (e y) (e z) := by
  have := congr_arg₂ (· * ·) (cycle_conj e a b c) (cycle_conj e x y z)
  simpa [-cycle_conj, ← mul_assoc] using this

@[simp]
theorem cycle_conj₂' : e⁻¹ * cycle a b c * cycle x y z * e =
    cycle (e⁻¹ a) (e⁻¹ b) (e⁻¹ c) * cycle (e⁻¹ x) (e⁻¹ y) (e⁻¹ z) :=
  cycle_conj₂ e⁻¹ a b c x y z

end Equiv
