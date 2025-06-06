import Mathlib.Data.Real.Basic

theorem solve_for_x (x y z : ℝ) 
  (h1 : 3 * x + 4 * y - 12 * z = 10) 
  (h2 : -2 * x - 3 * y + 9 * z = -4) : 
  x = 14 :=
by
  have eq1 := congrArg (λ t => 2 * t) h1
  have eq2 := congrArg (λ t => 3 * t) h2
  simp at eq1 eq2
  have h3 : 6 * x + 8 * y - 24 * z = 20 := eq1
  have h4 : -6 * x - 9 * y + 27 * z = -12 := eq2
  add_eqs : 6 * x + 8 * y - 24 * z + (-6 * x - 9 * y + 27 * z) = 20 + (-12) := by
    rw [h3, h4]
  simp at add_eqs
  have h5 : -y + 3 * z = 8 := add_eqs
  have h6 : y = 3 * z - 8 := by linarith
  rw [h6] at h1
  linarith