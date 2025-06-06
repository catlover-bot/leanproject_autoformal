import Mathlib.Data.Nat.Factorial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem amc12_2001_p21
  (a b c d : ℕ)
  (h₀ : a * b * c * d = 8!)
  (h₁ : a * b + a + b = 524)
  (h₂ : b * c + b + c = 146)
  (h₃ : c * d + c + d = 104) :
  ↑a - ↑d = (10 : ℤ) := by
  have h₄ : a * b = 522 := by linarith
  have h₅ : b * c = 144 := by linarith
  have h₆ : c * d = 102 := by linarith
  have h₇ : a * b * c * d = (a * b) * (c * d) := by ring
  rw [h₄, h₆] at h₇
  have h₈ : 522 * 102 = 8! := by norm_num
  rw [h₈] at h₇
  have h₉ : b = 12 := by
    have : 12 * 12 = 144 := by norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this h₅
  have h₁₀ : a = 43 := by
    have : 43 * 12 = 522 := by norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) this h₄
  have h₁₁ : c = 12 := by
    have : 12 * 12 = 144 := by norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this h₅
  have h₁₂ : d = 8 := by
    have : 12 * 8 = 102 := by norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) this h₆
  linarith