import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Nat

theorem power_mod (n : ℕ) (h : 0 < n) : (3^(2^n) - 1) % (2^(n + 3)) = 2^(n + 2) := by
  have h1 : 2 ≤ 2^n := by
    apply pow_le_pow
    norm_num
    exact h
  have h2 : 2^n ≤ 2^(n + 3) := by
    apply pow_le_pow_of_le_right
    norm_num
    linarith
  have h3 : 3^(2^n) ≡ 1 [MOD 2^(n + 3)] := by
    apply Nat.modeq_of_dvd
    use 2^(n + 2)
    rw [← Nat.sub_eq_iff_eq_add]
    apply Nat.pow_sub_pow_of_sub_dvd
    exact h1
  rw [Nat.modeq_iff_dvd] at h3
  cases h3 with k hk
  rw [hk, Nat.mul_sub_left_distrib, Nat.mul_one, Nat.add_sub_cancel]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.pow_lt_pow_of_lt_right (by norm_num) (by linarith)) h2)