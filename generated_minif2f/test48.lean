import Mathlib.Data.Real.Basic

theorem real_inequality : ∀ (a : ℝ), a * (2 - a) ≤ 1 := by
  intro a
  have h : a * (2 - a) = -a^2 + 2 * a := by ring
  rw [h]
  linarith [sq_nonneg a]