import Mathlib.Data.Real.Basic

theorem solve_for_x : ∀ (x : ℝ), 3 / 2 / 3 = x / 10 → x = 5 := by
  intro x h
  field_simp at h
  norm_num at h
  exact h.symm