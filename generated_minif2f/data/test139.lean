import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD

open Nat

theorem unique_n_for_gcd_lcm (n : ℕ) (h1 : 0 < n) (h2 : gcd n 40 = 10) (h3 : lcm n 40 = 280) : n = 70 := by
  have h4 : n * 40 = 280 * 10 := by
    rw [←h3, lcm_eq_mul_div_gcd, h2]
    ring
  have h5 : n * 40 = 2800 := by
    rw [h4]
    norm_num
  have h6 : n = 2800 / 40 := by
    rw [←h5]
    exact (Nat.mul_div_cancel_left n (by norm_num : 0 < 40))
  have h7 : n = 70 := by
    rw [h6]
    norm_num
  exact h7