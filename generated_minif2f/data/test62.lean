import Mathlib.Data.Real.Basic

theorem mathd_algebra_487
  (a b c d : ℝ)
  (h₀ : b = a^2)
  (h₁ : a + b = 1)
  (h₂ : d = c^2)
  (h₃ : c + d = 1) :
  real.sqrt ((a - c)^2 + (b - d)^2) = real.sqrt 10 :=
by
  have h₄ : b = 1 - a := by linarith
  have h₅ : d = 1 - c := by linarith
  rw [h₀, h₂, h₄, h₅]
  have h₆ : a^2 = 1 - a := by linarith
  have h₇ : c^2 = 1 - c := by linarith
  have h₈ : (a - c)^2 = a^2 - 2 * a * c + c^2 := by ring
  rw [h₆, h₇] at h₈
  have h₉ : a^2 + c^2 = 2 := by linarith
  have h₁₀ : -2 * a * c = -2 := by linarith
  rw [h₉, h₁₀] at h₈
  have h₁₁ : (a - c)^2 = 4 := by linarith
  have h₁₂ : (b - d)^2 = (1 - a - (1 - c))^2 := by ring
  rw [h₄, h₅] at h₁₂
  have h₁₃ : (b - d)^2 = (c - a)^2 := by ring
  rw [h₁₃, h₁₁]
  have h₁₄ : (a - c)^2 + (c - a)^2 = 8 := by linarith
  rw [h₁₄]
  norm_num