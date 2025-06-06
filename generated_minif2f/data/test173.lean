import Mathlib.Data.Real.Basic

theorem solve_for_x (x : ℝ) : 3 / 2 / 3 = x / 10 → x = 5 := by
  intro h₀
  have h₁ : 3 / 2 / 3 = 1 / 2 := by
    field_simp
    norm_num
  rw [h₁] at h₀
  linarith