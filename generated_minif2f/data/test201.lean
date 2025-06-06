import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic

namespace MyNamespace

theorem nat_int_difference (x y : ℕ) (h₁ : x + y = 17402) (h₂ : 10 ∣ x) (h₃ : x / 10 = y) : (↑x : ℤ) - ↑y = (14238 : ℤ) := by
  have h₄ : x = 10 * y := Nat.div_mul_cancel h₂
  rw [h₄] at h₁
  have h₅ : 10 * y + y = 17402 := by rw [←h₁, h₄]
  have h₆ : 11 * y = 17402 := by linarith
  have h₇ : y = 1582 := by norm_num at h₆; exact Nat.eq_of_mul_eq_mul_left (by norm_num) h₆
  rw [h₇] at h₄
  have h₈ : x = 15820 := by norm_num at h₄; exact h₄
  rw [h₈, h₇]
  norm_num

end MyNamespace