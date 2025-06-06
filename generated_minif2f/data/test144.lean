```lean
import Mathlib.Data.Real.Basic

open Classical

theorem solve_for_a (a : ℝ) (h₁ : a ≠ 0) (h₂ : 8⁻¹ / 4⁻¹ - a⁻¹ = 1) : a = -2 := by
  have h₃ : 8⁻¹ = 1 / 8 := by norm_num
  have h₄ : 4⁻¹ = 1 / 4 := by norm_num
  rw [h₃, h₄] at h₂
  have h₅ : (1 / 8) / (1 / 4) = 1 / 2 := by norm_num
  rw [h₅] at h₂
  have h₆ : 1 / 2 - a⁻¹ = 1 := h₂
  have h₇ : a⁻¹ = 1 / 2 - 1 := by linarith
  have h₈ : a⁻¹ = -1 / 2 := by norm_num at h₇; exact h₇
  have h₉ : a = -2 := by
    apply eq_inv_of_inv_eq
    rw [h₈]
    norm_num
  exact h₉
```