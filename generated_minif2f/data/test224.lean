import Mathlib.Data.Real.Basic

open Real

theorem abs_eq_sum_bounds (x : ℝ) : abs (x - 1) + abs x + abs (x + 1) = x + 2 → 0 ≤ x ∧ x ≤ 1 := by
  intro h
  have h_cases : x ≤ -1 ∨ (-1 < x ∧ x ≤ 0) ∨ (0 < x ∧ x ≤ 1) ∨ 1 < x := by
    by_cases h1 : x ≤ -1
    · left; exact h1
    by_cases h2 : x ≤ 0
    · right; left; constructor; linarith; exact h2
    by_cases h3 : x ≤ 1
    · right; right; left; constructor; linarith; exact h3
    right; right; right; linarith
  cases h_cases with h_neg h_cases
  · have : abs (x - 1) = -(x - 1) := abs_of_nonpos (by linarith)
    have : abs x = -x := abs_of_nonpos (by linarith)
    have : abs (x + 1) = -(x + 1) := abs_of_nonpos (by linarith)
    linarith
  cases h_cases with h_mid h_cases
  · cases h_mid with h_neg h_zero
    have : abs (x - 1) = -(x - 1) := abs_of_nonpos (by linarith)
    have : abs x = -x := abs_of_nonpos (by linarith)
    have : abs (x + 1) = x + 1 := abs_of_nonneg (by linarith)
    linarith
  cases h_cases with h_pos h_one
  · cases h_pos with h_zero h_one
    have : abs (x - 1) = -(x - 1) := abs_of_nonpos (by linarith)
    have : abs x = x := abs_of_nonneg (by linarith)
    have : abs (x + 1) = x + 1 := abs_of_nonneg (by linarith)
    linarith
  · have : abs (x - 1) = x - 1 := abs_of_nonneg (by linarith)
    have : abs x = x := abs_of_nonneg (by linarith)
    have : abs (x + 1) = x + 1 := abs_of_nonneg (by linarith)
    linarith