import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

theorem sum_divisible_by_9 (n : ℕ) (h₀ : 0 < n) (h₁ : 3 ∣ n) : 
  ((n + 4) + (n + 6) + (n + 8)) % 9 = 0 := 
by
  obtain ⟨k, rfl⟩ := h₁
  have : (3 * k + 4) + (3 * k + 6) + (3 * k + 8) = 9 * (k + 2) := by ring
  rw [this, Nat.add_mul_mod_self_left]
  exact Nat.zero_mod 9