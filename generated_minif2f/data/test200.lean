import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

theorem mathd_algebra_289
  (k t m n : ℕ)
  (h₀ : Nat.Prime m ∧ Nat.Prime n)
  (h₁ : t < k)
  (h₂ : (k^2 : ℤ) - m * k + n = 0)
  (h₃ : (t^2 : ℤ) - m * t + n = 0) :
  m^n + n^m + k^t + t^k = 20 := by
  have h₄ : (k - t : ℤ) * (k + t) = 0 := by
    linarith [h₂, h₃]
  have h₅ : k = t := by
    have : k - t = 0 := by
      linarith [h₄]
    exact Nat.eq_of_sub_eq_zero this
  have h₆ : m = 3 ∧ n = 2 := by
    have : (k^2 : ℤ) = m * k - n := by
      linarith [h₂]
    have : (t^2 : ℤ) = m * t - n := by
      linarith [h₃]
    have : m * k = n + k^2 := by
      linarith [h₂]
    have : m * t = n + t^2 := by
      linarith [h₃]
    have : m * k = m * t := by
      rw [h₅]
    have : m = 3 := by
      linarith [h₀.1, h₀.2, h₁, h₅]
    have : n = 2 := by
      linarith [h₀.1, h₀.2, h₁, h₅]
    exact ⟨this, ‹n = 2›⟩
  have h₇ : k = 3 ∧ t = 2 := by
    have : (k^2 : ℤ) = 3 * k - 2 := by
      linarith [h₂, h₆]
    have : (t^2 : ℤ) = 3 * t - 2 := by
      linarith [h₃, h₆]
    have : k = 3 := by
      linarith [h₁, h₅]
    have : t = 2 := by
      linarith [h₁, h₅]
    exact ⟨this, ‹t = 2›⟩
  rw [h₆.1, h₆.2, h₇.1, h₇.2]
  norm_num