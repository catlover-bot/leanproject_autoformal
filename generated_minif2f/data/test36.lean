import Mathlib.Algebra.Ring.Basic

theorem expand_and_multiply (x : ℝ) : (x + 1)^2 * x = x^3 + 2 * x^2 + x := by
  ring_nf