import Mathlib.Data.Real.Basic

theorem solve_system (s t : ℝ) (h₀ : s = 9 - 2 * t) (h₁ : t = 3 * s + 1) : s = 1 ∧ t = 4 := by
  -- Substitute s = 9 - 2t into t = 3s + 1
  rw [h₀] at h₁
  -- Simplify the equation
  have : t = 3 * (9 - 2 * t) + 1 := h₁
  simp at this
  -- Rearrange to solve for t
  linarith
  -- Now t = 4, substitute back to find s
  have ht : t = 4 := by linarith
  rw [ht] at h₀
  -- Simplify to find s
  have hs : s = 1 := by linarith
  -- Conclude s = 1 and t = 4
  exact ⟨hs, ht⟩