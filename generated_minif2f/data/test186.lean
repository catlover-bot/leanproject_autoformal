import Mathlib.Tactic

theorem evaluate_expression : 1 * 3^3 + 2 * 3^2 + 2 * 3 + 2 = 53 := by
  norm_num