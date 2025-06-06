import Mathlib.Data.Real.Basic

theorem solve_for_x (x y : ℝ) (h1 : x + y = 25) (h2 : x - y = 11) : x = 18 :=
by linarith [h1, h2]