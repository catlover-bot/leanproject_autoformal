import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic

open Nat

theorem nat_pos_div_eq (x y n : ℕ+) (h : (↑x / (4:ℝ) + y / 6 = (x + y) / n)) : n = 5 := by
  have h1 : (↑x / (4:ℝ) + y / 6) * n = (x + y) := by
    rw [←h]
    ring
  have h2 : (↑x * n / 4 + y * n / 6) = (x + y) := by
    rw [←h1]
    ring
  have h3 : (↑x * n / 4 + y * n / 6) * 12 = (x + y) * 12 := by
    rw [h2]
    ring
  have h4 : (3 * ↑x * n + 2 * y * n) = 12 * (x + y) := by
    linarith
  have h5 : 3 * ↑x * n + 2 * y * n = 12 * x + 12 * y := by
    rw [h4]
  have h6 : 3 * ↑x * n + 2 * y * n = 3 * 4 * x + 2 * 6 * y := by
    rw [h5]
  have h7 : 3 * ↑x * n + 2 * y * n = 3 * (4 * x) + 2 * (6 * y) := by
    ring
  have h8 : 3 * ↑x * n + 2 * y * n = 3 * (4 * x) + 2 * (6 * y) := by
    rw [h7]
  have h9 : 3 * ↑x * n = 3 * (4 * x) := by
    linarith
  have h10 : ↑x * n = 4 * x := by
    linarith
  have h11 : n = 4 := by
    linarith
  have h12 : 2 * y * n = 2 * (6 * y) := by
    linarith
  have h13 : y * n = 6 * y := by
    linarith
  have h14 : n = 6 := by
    linarith
  have h15 : n = 5 := by
    linarith
  exact h15