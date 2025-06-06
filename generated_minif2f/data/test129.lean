import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real

theorem solve_for_a (a : ℝ) : sqrt (4 + sqrt (16 + 16 * a)) + sqrt (1 + sqrt (1 + a)) = 6 → a = 8 := by
  intro h
  have h1 : sqrt (4 + sqrt (16 + 16 * a)) = 4 := by
    have : sqrt (4 + sqrt (16 + 16 * a)) ≤ 4 := by
      apply sqrt_le_sqrt
      linarith
    have : 4 ≤ sqrt (4 + sqrt (16 + 16 * a)) := by
      rw [← h]
      apply le_add_of_nonneg_right
      apply sqrt_nonneg
    exact le_antisymm this ‹_›
  have h2 : sqrt (1 + sqrt (1 + a)) = 2 := by
    have : sqrt (1 + sqrt (1 + a)) ≤ 2 := by
      apply sqrt_le_sqrt
      linarith
    have : 2 ≤ sqrt (1 + sqrt (1 + a)) := by
      rw [← h]
      apply le_add_of_nonneg_left
      apply sqrt_nonneg
    exact le_antisymm this ‹_›
  rw [h1, h2] at h
  linarith