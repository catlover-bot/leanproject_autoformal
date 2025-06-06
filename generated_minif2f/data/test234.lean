import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Nat

theorem prime_7_plus_30n (n : ℕ) : ¬ prime (7 + 30 * n) → 6 ≤ n := by
  intro h
  by_contra h'
  push_neg at h'
  have : 7 + 30 * n < 7 + 30 * 6 := by
    linarith
  have : 7 + 30 * n < 187 := by
    norm_num
    exact this
  have : prime (7 + 30 * n) := by
    interval_cases n <;> norm_num
  contradiction