```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic

theorem nat_div_difference (x y : ℕ) (h₁ : x + y = 17402) (h₂ : 10 ∣ x) (h₃ : x / 10 = y) : 
  (↑x - ↑y : ℤ) = 14238 := 
by
  have hx : x = 10 * y := Nat.div_mul_cancel (Nat.dvd_of_div_eq h₃)
  rw [hx] at h₁
  have hy : 11 * y = 17402 := by linarith
  have y_val : y = 1582 := by norm_num at hy; exact Nat.eq_of_mul_eq_mul_left (by norm_num) hy
  have x_val : x = 10 * 1582 := by rw [hx, y_val]
  have x_val' : x = 15820 := by norm_num at x_val; exact x_val
  rw [x_val', y_val]
  norm_num
```