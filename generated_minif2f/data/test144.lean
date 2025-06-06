import Mathlib.Data.Real.Basic

theorem solve_for_a (a : ℝ) (h₀ : a ≠ 0) (h₁ : 8⁻¹ / 4⁻¹ - a⁻¹ = 1) : a = -2 := by
  have h₂ : 8⁻¹ / 4⁻¹ = 1 / 8 * 4 := by rw [div_eq_mul_inv]
  rw [h₂, mul_inv_cancel_left₀ (by norm_num : (4 : ℝ) ≠ 0)] at h₁
  have h₃ : 1 / 8 * 4 = 1 / 2 := by norm_num
  rw [h₃] at h₁
  have h₄ : 1 / 2 - a⁻¹ = 1 := h₁
  have h₅ : a⁻¹ = 1 / 2 - 1 := by linarith
  have h₆ : a⁻¹ = -1 / 2 := by norm_num at h₅; exact h₅
  have h₇ : a = -2 := by rw [eq_inv_of_eq_inv h₆]; norm_num
  exact h₇