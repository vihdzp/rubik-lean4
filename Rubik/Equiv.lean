import Mathlib.GroupTheory.Perm.Basic

/-!
We prove various auxiliary results about equivalences.
-/

namespace Equiv

variable {α : Type*}

@[simp]
theorem symm_mul (e₁ e₂ : Perm α) : (e₁ * e₂).symm = e₂.symm * e₁.symm :=
  rfl

variable (e : Perm α) (a b c d : α) [DecidableEq α]

@[simp]
theorem swap_conj : e * (swap a b) * e⁻¹ = swap (e a) (e b) := by
  aesop (add norm swap_apply_def)

@[simp]
theorem swap_conj' : e⁻¹ * (swap a b) * e = swap (e⁻¹ a) (e⁻¹ b) :=
  swap_conj e⁻¹ a b

@[simp]
theorem swap_conj₂ : e * (swap a b) * (swap c d) * e⁻¹ =
    swap (e a) (e b) * swap (e c) (e d) := by
  have := congr_arg₂ (· * ·) (swap_conj e a b) (swap_conj e c d)
  simpa [-swap_conj, ← mul_assoc] using this

@[simp]
theorem swap_conj'₂ : e⁻¹ * (swap a b) * (swap c d) * e =
    swap (e⁻¹ a) (e⁻¹ b) * swap (e⁻¹ c) (e⁻¹ d) :=
  swap_conj₂ e⁻¹ a b c d

/-- A cyclic permutation `a → b → c → a`. -/
def cycle₃ : Perm α :=
  if a ≠ b ∧ b ≠ c ∧ c ≠ a then swap a b * swap b c else Equiv.refl _

theorem cycle₃_fst {a b c : α} (h₂ : b ≠ c) (h₃ : c ≠ a) : cycle₃ a b c a = b := by
  rw [cycle₃]
  aesop (add norm swap_apply_def)

theorem cycle₃_snd {a b c : α} (h₁ : a ≠ b) (h₃ : c ≠ a) : cycle₃ a b c b = c := by
  rw [cycle₃]
  aesop (add norm swap_apply_def)

theorem cycle₃_thd {a b c : α} (h₁ : a ≠ b) (h₂ : b ≠ c) : cycle₃ a b c c = a := by
  rw [cycle₃]
  aesop (add norm swap_apply_def)

theorem cycle₃_cyclic : cycle₃ a b c = cycle₃ b c a := by
  rw [cycle₃, cycle₃]
  aesop (add norm swap_apply_def)

end Equiv
