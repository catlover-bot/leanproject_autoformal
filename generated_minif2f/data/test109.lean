import Mathlib.Data.Real.Basic

theorem algebraic_identity (x : ℝ) : (x + 3) * (2 * x - 6) = 2 * x^2 - 18 := by
  calc
    (x + 3) * (2 * x - 6) = x * (2 * x) + x * (-6) + 3 * (2 * x) + 3 * (-6) := by ring
    _ = 2 * x^2 - 6 * x + 6 * x - 18 := by ring
    _ = 2 * x^2 - 18 := by ring