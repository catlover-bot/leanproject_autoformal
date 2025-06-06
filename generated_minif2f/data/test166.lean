import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Int

theorem divisibility_by_11 (n : ℕ) : 11 ∣ (10^n - (-1 : ℤ)^n) := by
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    rw [pow_succ, pow_succ, mul_comm 10, mul_comm (-1 : ℤ)]
    have h : 10 * 10^n - (-1) * (-1)^n = 10 * 10^n - (-1)^n * (-1) := by ring
    rw [h]
    have : 11 ∣ 10 * 10^n - 10 * (-1)^n := by
      apply dvd_mul_of_dvd_right
      exact ih
    have : 11 ∣ 10 * (-1)^n - (-1)^n := by
      apply dvd_sub
      apply dvd_mul_of_dvd_right
      norm_num
    exact dvd_add this ‹11 ∣ 10 * 10^n - 10 * (-1)^n›