import Mathlib.Data.Real.Basic

open Real

theorem polynomial_identity : ∀ (x : ℝ), (x + 3) * (2 * x - 6) = 2 * x^2 - 18 := by
  intro x
  ring