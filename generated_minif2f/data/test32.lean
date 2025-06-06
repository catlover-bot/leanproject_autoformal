import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

theorem mathd_numbertheory_277
  (m n : ℕ)
  (h₀ : Nat.gcd m n = 6)
  (h₁ : Nat.lcm m n = 126) :
  60 ≤ m + n := by
  have h₂ : m * n = Nat.gcd m n * Nat.lcm m n := Nat.gcd_mul_lcm m n
  rw [h₀, h₁] at h₂
  have h₃ : m * n = 756 := h₂
  have h₄ : m = 6 * (m / 6) := Nat.mul_div_cancel' (Nat.dvd_gcd_left h₀)
  have h₅ : n = 6 * (n / 6) := Nat.mul_div_cancel' (Nat.dvd_gcd_right h₀)
  rw [h₄, h₅] at h₃
  have h₆ : (m / 6) * (n / 6) = 21 := by
    rw [←Nat.mul_div_assoc _ (Nat.dvd_gcd_left h₀), ←Nat.mul_div_assoc _ (Nat.dvd_gcd_right h₀)]
    exact Nat.div_eq_of_eq_mul_right (by norm_num) h₃
  have h₇ : 1 ≤ m / 6 := Nat.div_pos (Nat.gcd_dvd_left m n) (by norm_num)
  have h₈ : 1 ≤ n / 6 := Nat.div_pos (Nat.gcd_dvd_right m n) (by norm_num)
  have h₉ : 1 ≤ m / 6 + n / 6 := by linarith
  have h₁₀ : 6 * (m / 6 + n / 6) = m + n := by ring
  rw [h₁₀]
  linarith [h₆, h₇, h₈]