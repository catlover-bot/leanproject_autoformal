import Mathlib.Data.Real.Basic

namespace RealTheorems

theorem ab_inequality (a b : ℝ) (h : a^2 + b^2 = 1) : a * b + (a - b) ≤ 1 := by
  have h1 : a^2 ≤ 1 := by
    have h2 : b^2 ≥ 0 := sq_nonneg b
    linarith
  have h3 : b^2 ≤ 1 := by
    have h4 : a^2 ≥ 0 := sq_nonneg a
    linarith
  have h5 : a * b ≤ 1/2 := by
    have h6 : 2 * (a^2 + b^2) = 2 := by rw [h, mul_one]
    have h7 : (a + b)^2 = a^2 + 2 * a * b + b^2 := by ring
    have h8 : (a - b)^2 = a^2 - 2 * a * b + b^2 := by ring
    have h9 : (a + b)^2 + (a - b)^2 = 2 * (a^2 + b^2) := by
      rw [h7, h8]
      ring
    rw [h6] at h9
    have h10 : (a + b)^2 + (a - b)^2 = 2 := h9
    have h11 : (a + b)^2 ≥ 0 := sq_nonneg (a + b)
    have h12 : (a - b)^2 ≥ 0 := sq_nonneg (a - b)
    linarith
  linarith

end RealTheorems