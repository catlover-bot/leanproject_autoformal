import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD
import Mathlib.Tactic.Linarith

open Nat

theorem mathd_numbertheory_711
  (m n : ℕ)
  (h₀ : 0 < m ∧ 0 < n)
  (h₁ : gcd m n = 8)
  (h₂ : lcm m n = 112) :
  72 ≤ m + n :=
begin
  have h₃ : m * n = gcd m n * lcm m n := Nat.gcd_mul_lcm m n,
  rw [h₁, h₂] at h₃,
  have h₄ : m * n = 8 * 112 := h₃,
  have h₅ : m * n = 896 := by norm_num [h₄],
  have h₆ : m = 8 * (m / 8) := (Nat.mul_div_cancel' (Nat.dvd_gcd_left h₁)).symm,
  have h₇ : n = 8 * (n / 8) := (Nat.mul_div_cancel' (Nat.dvd_gcd_right h₁)).symm,
  rw [h₆, h₇] at h₅,
  have h₈ : (m / 8) * (n / 8) = 14 := by
    rw [mul_assoc, mul_assoc, mul_comm 8 8, ← mul_assoc, ← mul_assoc, Nat.mul_right_inj (by norm_num : 0 < 8)],
    exact h₅,
  have h₉ : 1 ≤ m / 8 ∧ 1 ≤ n / 8 := ⟨Nat.div_pos h₀.1 (by norm_num), Nat.div_pos h₀.2 (by norm_num)⟩,
  have h₁₀ : 1 ≤ m / 8 + n / 8 := by linarith,
  have h₁₁ : m / 8 + n / 8 ≥ 15 := by
    have : (m / 8) * (n / 8) ≤ ((m / 8 + n / 8) / 2) ^ 2 := Nat.mul_le_mul_of_nonneg_left (Nat.div_le_self _ _) (by norm_num),
    linarith [h₈, this],
  have h₁₂ : m + n = 8 * (m / 8) + 8 * (n / 8) := by rw [h₆, h₇],
  have h₁₃ : m + n = 8 * (m / 8 + n / 8) := by rw [← mul_add, h₁₂],
  linarith [h₁₁, h₁₃],
end