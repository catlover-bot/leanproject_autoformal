import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Nat

theorem gcd_lcm_n_eq_70 : ∀ (n : ℕ), 0 < n → gcd n 40 = 10 → lcm n 40 = 280 → n = 70 :=
  fun n hn h_gcd h_lcm =>
  have h1 : n * 40 = gcd n 40 * lcm n 40 := Nat.gcd_mul_lcm n 40
  have h2 : n * 40 = 10 * 280 := by rw [h_gcd, h_lcm] at h1; exact h1
  have h3 : n * 40 = 2800 := by norm_num at h2; exact h2
  have h4 : n = 2800 / 40 := by rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 40)] at h3; exact h3
  have h5 : n = 70 := by norm_num at h4; exact h4
  h5