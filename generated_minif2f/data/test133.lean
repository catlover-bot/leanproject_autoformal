import Mathlib.Data.Real.Basic

theorem sum_of_x_and_y (x y : ℝ) (h1 : 3 * y = x) (h2 : 2 * x + 5 * y = 11) : x + y = 4 := by
  rw [←h1] at h2
  have : 2 * (3 * y) + 5 * y = 11 := h2
  simp at this
  have : 11 * y = 11 := this
  have : y = 1 := by linarith
  have : x = 3 * y := h1
  rw [this, `y = 1`]
  linarith