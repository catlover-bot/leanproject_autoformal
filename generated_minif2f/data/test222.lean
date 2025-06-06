import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic.Ring

open Real

theorem power_identity (m n p q : ℝ) (h₀ : p = 2 ^ m) (h₁ : q = 3 ^ n) : p^(2 * n) * (q^m) = 12^(m * n) := by
  rw [h₀, h₁]
  have h2 : (2 ^ m)^(2 * n) = 2^(2 * m * n) := by rw [pow_mul]
  have h3 : (3 ^ n)^m = 3^(m * n) := by rw [pow_mul]
  rw [h2, h3]
  have h4 : 12 = 2^2 * 3 := by norm_num
  rw [h4, pow_mul, pow_mul]
  ring_nf
  exact rfl