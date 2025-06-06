import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real

theorem problem (a b : ℝ) : a^2 * b^3 = 32 / 27 ∧ a / b^3 = 27 / 4 → a + b = 8 / 3 := by
  intro h
  cases h with
  | intro h1 h2 =>
    have h3 : a = 3 * b := by
      field_simp at h2
      linarith
    rw [h3] at h1
    have h4 : (3 * b)^2 * b^3 = 32 / 27 := h1
    ring_nf at h4
    have h5 : 9 * b^5 = 32 / 27 := h4
    field_simp at h5
    have h6 : b^5 = 32 / 243 := by
      linarith
    have h7 : b = 2 / 3 := by
      apply pow_eq_of_pow_eq_one
      norm_num
      exact h6
    rw [h7] at h3
    have h8 : a = 3 * (2 / 3) := h3
    norm_num at h8
    rw [h8, h7]
    norm_num