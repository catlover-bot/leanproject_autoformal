import Mathlib.Data.Real.Basic

theorem simplify_expression (n : ℕ) (h₀ : n = 11) : (1 / 4)^(n + 1) * 2^(2 * n) = 1 / 4 := by
  rw [h₀]
  have h₁ : (1 / 4)^(11 + 1) = (1 / 4)^12 := by rfl
  have h₂ : 2^(2 * 11) = 2^22 := by rfl
  rw [h₁, h₂]
  have h₃ : (1 / 4)^12 = 4^(-12 : ℤ) := by rfl
  have h₄ : 2^22 = 4^11 := by norm_num
  rw [h₃, h₄]
  have h₅ : 4^(-12 : ℤ) * 4^11 = 4^(-1 : ℤ) := by
    rw [← Int.add_neg_one, Int.add_comm]
    exact pow_add 4 (-12 : ℤ) 11
  rw [h₅]
  norm_num