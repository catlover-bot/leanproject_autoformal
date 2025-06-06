import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD

theorem mathd_numbertheory_222
(b : ℕ)
(h₀ : Nat.lcm 120 b = 3720)
(h₁ : Nat.gcd 120 b = 8) :
b = 248 :=
by
  have h : 8 * 3720 = 120 * b := by
    rw [Nat.gcd_mul_lcm h₁, h₀]
  have : b = (8 * 3720) / 120 := by
    rw [←h]
    exact Nat.mul_div_cancel_left b (Nat.pos_of_ne_zero (by decide))
  norm_num at this
  exact this