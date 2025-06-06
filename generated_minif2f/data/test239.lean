import Mathlib.Data.Real.Basic

lemma solve_for_x : ∀ (x : ℝ), 5 + 500 / 100 * 10 = 110 / 100 * x → x = 50 := by
  intro x h
  norm_num at h
  linarith