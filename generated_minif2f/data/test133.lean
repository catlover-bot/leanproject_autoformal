import Mathlib.Data.Real.Basic

namespace RealTheorems

theorem solve_system (x y : ℝ) (h1 : 3 * y = x) (h2 : 2 * x + 5 * y = 11) : x + y = 4 := by
  have h3 : 2 * (3 * y) + 5 * y = 11 := by rw [←h1]
  have h4 : 6 * y + 5 * y = 11 := by rw [mul_assoc]
  have h5 : 11 * y = 11 := by rw [←add_mul, h4]
  have h6 : y = 1 := by linarith
  have h7 : x = 3 * 1 := by rw [h1, h6]
  have h8 : x = 3 := by norm_num at h7
  linarith

end RealTheorems