import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Complex

theorem complex_inequality (a b : ℂ) 
  (ha : a^3 - 8 = 0) 
  (hb : b^3 - 8 * b^2 - 8 * b + 64 = 0) : 
  complex.abs (a - b) ≤ 2 * real.sqrt 21 := 
by
  have ha' : a^3 = 8 := by linarith
  have hb' : b^3 - 8 * b^2 - 8 * b = -64 := by linarith
  have h : (a - 2) * (a^2 + 2 * a + 4) = 0 := by
    have : a^3 - 8 = (a - 2) * (a^2 + 2 * a + 4) := by ring
    rw [ha] at this
    linarith
  cases eq_or_ne a 2 with ha2 ha2
  · rw [ha2]
    have : b^3 - 8 * b^2 - 8 * b + 64 = (b - 4)^3 := by ring
    rw [hb, this] at hb'
    have hb4 : b = 4 := by
      have : (b - 4)^3 = 0 := by linarith
      rw [sub_eq_zero] at this
      exact this
    rw [hb4]
    norm_num
  · have : a^2 + 2 * a + 4 = 0 := by
      cases eq_or_ne (a - 2) 0 with ha2' ha2'
      · contradiction
      · exact eq_zero_of_mul_eq_zero_left ha2' h
    have : b^3 - 8 * b^2 - 8 * b + 64 = (b - 4)^3 := by ring
    rw [hb, this] at hb'
    have hb4 : b = 4 := by
      have : (b - 4)^3 = 0 := by linarith
      rw [sub_eq_zero] at this
      exact this
    rw [hb4]
    have : a^2 + 2 * a + 4 = 0 := this
    have : complex.abs (a - 4) ≤ 2 * real.sqrt 21 := by
      have : complex.abs (a - 4) = complex.abs (a - 2 - 2) := by ring
      rw [this]
      have : complex.abs (a - 2 - 2) ≤ complex.abs (a - 2) + complex.abs 2 := abs_sub_le _ _ _
      have : complex.abs 2 = 2 := by norm_num
      linarith
    exact this