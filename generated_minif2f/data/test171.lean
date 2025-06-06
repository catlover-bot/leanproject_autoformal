import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Data.Real.Basic

open Real

lemma cube_root_identity (r : ℝ) (h : r^((1:ℝ) / 3) + 1 / r^((1:ℝ) / 3) = 3) : r^3 + 1 / r^3 = 5778 :=
by
  set x := r^((1:ℝ) / 3) with hx
  have hx_ne_zero : x ≠ 0 := by
    intro h0
    rw [h0, zero_add] at h
    have : 1 / 0 = 3 := h
    norm_num at this
  have h1 : x + 1 / x = 3 := h
  have h2 : (x + 1 / x)^3 = 27 := by
    rw [h1]
    norm_num
  have h3 : x^3 + 3 * x + 3 * (1 / x) + 1 / x^3 = 27 := by
    rw [add_div, add_div, add_div, add_div, div_self hx_ne_zero, div_self hx_ne_zero, div_self hx_ne_zero]
    ring
  have h4 : x^3 + 1 / x^3 = 27 - 3 * (x + 1 / x) := by
    linarith
  rw [h1] at h4
  norm_num at h4
  have h5 : r^3 = x^3 := by
    rw [hx]
    ring
  have h6 : 1 / r^3 = 1 / x^3 := by
    rw [hx]
    field_simp
    ring
  rw [h5, h6]
  exact h4