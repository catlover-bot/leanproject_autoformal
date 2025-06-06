import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

lemma mod_five_double (n : ℕ) (h : n % 5 = 3) : (2 * n) % 5 = 1 := by
  have h₁ : 2 * n % 5 = (2 * 3) % 5 := by rw [h]
  norm_num at h₁
  exact h₁

theorem double_mod_five (n : ℕ) : n % 5 = 3 → (2 * n) % 5 = 1 :=
  mod_five_double n