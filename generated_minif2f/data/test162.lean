```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic

theorem solve_for_x (x y : ℕ) (h₀ : 0 < x ∧ 0 < y) (h₁ : 5 * x = y) (h₂ : (↑x - (3:ℤ)) + (y - (3:ℤ)) = 30) : x = 6 := by
  have h₃ : (↑x - 3) + (5 * x - 3) = 30 := by
    rw [h₁] at h₂
    exact h₂
  have h₄ : (↑x + 5 * x - 6) = 30 := by
    linarith
  have h₅ : 6 * x - 6 = 30 := by
    rw [←Int.coe_nat_add, Int.coe_nat_mul] at h₄
    exact h₄
  have h₆ : 6 * x = 36 := by
    linarith
  have h₇ : x = 6 := by
    linarith
  exact h₇
```