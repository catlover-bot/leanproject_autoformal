import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Nat

theorem gcd_21n_plus_4_14n_plus_3 (n : ℕ) (h : 0 < n) : gcd (21 * n + 4) (14 * n + 3) = 1 := by
  have h1 : gcd (21 * n + 4) (14 * n + 3) = gcd (14 * n + 3) ((21 * n + 4) % (14 * n + 3)) := gcd_rec (21 * n + 4) (14 * n + 3)
  have h2 : (21 * n + 4) % (14 * n + 3) = 7 * n + 1 := by
    calc
      (21 * n + 4) % (14 * n + 3) = (21 * n + 4) - ((21 * n + 4) / (14 * n + 3)) * (14 * n + 3) := rfl
      _ = (21 * n + 4) - 1 * (14 * n + 3) := by
        have : 21 * n + 4 < 2 * (14 * n + 3) := by linarith
        have : (21 * n + 4) / (14 * n + 3) = 1 := by linarith
        rw [this]
      _ = 21 * n + 4 - 14 * n - 3 := rfl
      _ = 7 * n + 1 := by ring
  rw [h1, h2]
  have h3 : gcd (14 * n + 3) (7 * n + 1) = gcd (7 * n + 1) ((14 * n + 3) % (7 * n + 1)) := gcd_rec (14 * n + 3) (7 * n + 1)
  have h4 : (14 * n + 3) % (7 * n + 1) = 2 := by
    calc
      (14 * n + 3) % (7 * n + 1) = (14 * n + 3) - ((14 * n + 3) / (7 * n + 1)) * (7 * n + 1) := rfl
      _ = (14 * n + 3) - 2 * (7 * n + 1) := by
        have : 14 * n + 3 < 3 * (7 * n + 1) := by linarith
        have : (14 * n + 3) / (7 * n + 1) = 2 := by linarith
        rw [this]
      _ = 14 * n + 3 - 14 * n - 2 := rfl
      _ = 1 := by ring
  rw [h3, h4]
  exact gcd_one_right 1