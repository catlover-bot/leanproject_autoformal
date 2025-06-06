import Mathlib.Data.Real.Basic

theorem real_numbers_proof (n x : ℝ) (h1 : n + x = 97) (h2 : n + 5 * x = 265) : n + 2 * x = 139 :=
by
  have h3 : 4 * x = 168 := by linarith
  have h4 : x = 42 := by linarith
  have h5 : n = 55 := by linarith
  linarith