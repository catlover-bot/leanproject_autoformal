import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Data.Real.Basic

open Real

theorem problem (a b : ℝ) (h : a^2 + b^2 = 1) : a * b + ∥a - b∥ ≤ 1 := by
  have h₁ : a^2 + b^2 = 1 := h
  have h₂ : (a - b)^2 = a^2 - 2 * a * b + b^2 := by ring
  have h₃ : a^2 + b^2 - 2 * a * b = 1 - 2 * a * b := by rw [h₁]
  have h₄ : (a - b)^2 = 1 - 2 * a * b := by rw [h₂, h₃]
  have h₅ : ∥a - b∥ = Real.sqrt ((a - b)^2) := by rw [Real.norm_eq_abs, abs_eq_self.mpr (Real.sqrt_nonneg _)]
  rw [h₅, h₄]
  have h₆ : Real.sqrt (1 - 2 * a * b) ≤ 1 := by
    apply Real.sqrt_le_sqrt
    linarith
  linarith [h₆]