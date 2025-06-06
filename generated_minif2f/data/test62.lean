import Mathlib.Data.Real.Basic
import Mathlib.Algebra.GroupPower.Basic

open Real

theorem mathd_algebra_487
  (a b c d : ℝ)
  (h₀ : b = a^2)
  (h₁ : a + b = 1)
  (h₂ : d = c^2)
  (h₃ : c + d = 1) :
  sqrt ((a - c)^2 + (b - d)^2) = sqrt 10 :=
by
  have ha : a^2 + a - 1 = 0 := by rw [←h₀, ←h₁]; ring
  have hc : c^2 + c - 1 = 0 := by rw [←h₂, ←h₃]; ring
  have a_values : a = 1 ∨ a = -1 :=
    by simpa using eq_or_eq_neg_of_add_eq_zero (eq_neg_of_add_eq_zero ha)
  have c_values : c = 1 ∨ c = -1 :=
    by simpa using eq_or_eq_neg_of_add_eq_zero (eq_neg_of_add_eq_zero hc)
  cases a_values with ha1 ha1
  · cases c_values with hc1 hc1
    · rw [ha1, hc1, h₀, h₂]
      simp
    · rw [ha1, hc1, h₀, h₂]
      simp
  · cases c_values with hc1 hc1
    · rw [ha1, hc1, h₀, h₂]
      simp
    · rw [ha1, hc1, h₀, h₂]
      simp
  all_goals
    rw [h₀, h₂]
    simp
    ring_nf
    norm_num
    rw [sqrt_sq]
    norm_num
    linarith
    linarith
    linarith
    linarith