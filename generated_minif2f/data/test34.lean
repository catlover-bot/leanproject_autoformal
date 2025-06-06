import Mathlib.Data.Real.Basic

theorem solve_equations (n x : ℝ) : n + x = 97 → n + 5 * x = 265 → n + 2 * x = 139 :=
  by
    intros h1 h2
    have h3 : 4 * x = 168 := by linarith
    have h4 : x = 42 := by linarith
    have h5 : n + 42 = 97 := by rw [←h1, h4]
    have h6 : n = 55 := by linarith
    linarith