import Mathlib.Data.Real.Basic

open Real

theorem xyz_product_one (x y z : ℝ) 
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) 
  (h₁ : x + 1/y = 4) 
  (h₂ : y + 1/z = 1) 
  (h₃ : z + 1/x = 7/3) : 
  x * y * z = 1 := 
by
  have hx : x = 4 - 1/y := by linarith
  have hy : y = 1 - 1/z := by linarith
  have hz : z = 7/3 - 1/x := by linarith
  have hxy : x * y = 4 * (1 - 1/z) - 1 := by
    rw [hx, hy]
    ring
  have hxyz : x * y * z = (4 * (1 - 1/z) - 1) * z := by
    rw [hxy]
  rw [hz] at hxyz
  have : (4 * (1 - 1/z) - 1) * (7/3 - 1/x) = 1 := by
    field_simp [h₀.1, h₀.2.1, h₀.2.2]
    ring
  rw [←hxyz]
  exact this