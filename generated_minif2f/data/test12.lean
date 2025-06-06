import Mathlib.Data.Real.Basic

theorem ratio_of_z_and_x (x y z : ℝ) (hx : x ≠ 0) (h1 : 2 * x = 5 * y) (h2 : 7 * y = 10 * z) : z / x = 7 / 25 := 
by
  have hy : y = (2 / 5) * x := by
    field_simp [hx]
    linarith
  have hz : z = (7 / 10) * y := by
    field_simp
    linarith
  rw [hy] at hz
  rw [hz]
  field_simp [hx]
  norm_num