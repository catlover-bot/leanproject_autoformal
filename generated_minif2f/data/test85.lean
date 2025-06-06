import Mathlib.Data.Real.Basic

theorem complete_square (x y : ℝ) : x^2 + 8 * x + y^2 - 6 * y = 0 → (x + 4)^2 + (y - 3)^2 = 5^2 := by
  intro h
  have hx : x^2 + 8 * x = (x + 4)^2 - 16 := by
    calc
      x^2 + 8 * x = (x + 4)^2 - 16 := by ring
  have hy : y^2 - 6 * y = (y - 3)^2 - 9 := by
    calc
      y^2 - 6 * y = (y - 3)^2 - 9 := by ring
  calc
    (x + 4)^2 + (y - 3)^2 = (x^2 + 8 * x + y^2 - 6 * y) + 25 := by
      rw [hx, hy]
      ring
    _ = 0 + 25 := by rw [h]
    _ = 25 := by ring
    _ = 5^2 := by norm_num